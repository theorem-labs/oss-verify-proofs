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
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require ImgA RA_mqq1 RA_seql.

Module RA_sh6p.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1 RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@DB2]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfx.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp wend bufp bufsize : Z) (mode : word) (CK S0 N B Sr l lo : Z) (dn : nat) (p bs jd : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    let k := Z.of_nat (length (firstn (Z.to_nat N) (p ++ bs))) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (S0, S0 + Z.of_nat dn)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Fp (snfile z64 wend bufp bufp bufp bufsize mode CK)
    /\ rw_cells rsegs m' CK [C8 (Z_to_bv 64 (S0 + k)); C8 (Z_to_bv 64 (N - k))]
    /\ rw_cells rsegs m' S0 [CB dn (firstn (Z.to_nat N) (p ++ bs) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat k)) jd)]
    /\ bytes_at rsegs m' B p /\ bytes_at rsegs m' Sr bs.

(* [comment removed for export] *)
Definition sfw (S0 : Z) (dn : nat) (Sr l B SB : Z) (K : nat) (m : word -> option byte) : Prop :=
     asan_memcpy_cells m /\ range_ok m S0 (Z.of_nat dn) /\ (l = 0%Z \/ range_ok m Sr l)
  /\ bytes_at rsegs m SB (zeros K) /\ zsh_bounds SB K B (B + 80)
  /\ (2147446784 <= SB)%Z.   (* [comment removed for export] *)
Lemma lowP_sfw : forall S0 dn Sr l B SB K, (0 <= l)%Z -> lowP (sfw S0 dn Sr l B SB K).
Proof.
  (intros S0 dn Sr l B SB K Hl W m m' MU HW; (first [ intro dR_6; dand6 dR_6 as C1 R1 R2 ZS ZB SBL | intros (C1 & R1 & R2 & ZS & ZB & SBL) ])). (first [ pose proof (ZB) as dR_1; dand4 dR_1 as B1 B2 B3 _ | pose proof ZB as (B1 & B2 & B3 & _) ]).
  split; [exact (lowP_asan_memcpy_cells W m m' MU HW C1)|].
  split; [exact (lowP_range_ok S0 (Z.of_nat dn) ltac:(lia) W m m' MU HW R1)|].
  split; [destruct R2 as [R2|R2]; [left; exact R2| right; exact (lowP_range_ok Sr l Hl W m m' MU HW R2)]|].
  split; [|exact (conj ZB SBL)].
  eapply bytes_at_transport; [exact ZS| exact MU| apply low_disjoint; [exact HW|]].
  rewrite zeros_length. unfold in_zone, kHighShadowEnd_z, kHighMemBeg_z in *. lia.
Qed.
Local Ltac low_lemma P ::=
  lazymatch P with
  | sfw ?S0 ?dn ?Sr ?l ?B ?SB ?K => constr:(lowP_sfw S0 dn Sr l B SB K ltac:(lia))
  | _ => low_lemma_base P
  end.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
Ltac open_sfw H := let a := fresh "CE" in let b := fresh "RD" in let c := fresh "RS" in let d := fresh "ZS" in let e := fresh "ZB" in
  let f := fresh "SBL" in (first [ pose proof (H) as dR_2; dex5 dR_2 as a b c d e; rename dR_2 into f | pose proof (H) as dR_2; dand6 dR_2 as a b c d e f | pose proof H as (a & b & c & d & e & f) ]).

Section SnWrite.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : word -> option byte)
            (Fp wend bufp bufsize : Z) (mode : word) (CK S0 N B Sr l lo : Z) (dn : nat) (p bs jd : list byte)
            (ZSB : Z) (ZK : nat).
  Hypothesis LEN : length bs = Z.to_nat l.
  Hypothesis N0 : (0 <= N)%Z.
  Hypothesis N31 : (N < 2^31)%Z.   (* [comment removed for export] *)
  Hypothesis ND : (N + 1 <= Z.of_nat dn)%Z.
  Hypothesis Hl : (0 <= l < 2^63)%Z.
  Hypothesis HB : (B + Z.of_nat (length p) < 2^63)%Z.
  Hypothesis Hbuf : (0 <= bufp < 2^64)%Z.
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 2304)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis KH : dst_zone S0 (Z.of_nat dn).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis L1 : (S0 + Z.of_nat dn <= lo)%Z.
  Hypothesis L2 : (bv_unsigned sp <= B)%Z.
  Hypothesis L3 : (B + 80 <= Fp)%Z.
  Hypothesis L4 : (CK = Fp + 232)%Z.
  Hypothesis L5 : (Sr + l <= B)%Z.
  Hypothesis L6 : (~ (lo < Sr + l /\ Sr < bv_unsigned sp))%Z.
  Hypothesis L7 : (~ (S0 < Sr + l /\ Sr < S0 + Z.of_nat dn))%Z.   (* [comment removed for export] *)
  Hypothesis LP : (Z.of_nat (length p) <= 80)%Z.
  Hypothesis DB : (0 <= S0 /\ S0 + Z.of_nat dn <= 2^64)%Z.
  Hypothesis CB_ : (0 <= CK /\ CK + 16 <= 2^64)%Z.
  Hypothesis FB : (0 <= Fp /\ Fp + 232 <= 2^64)%Z.
  Hypothesis BB : (0 <= B /\ B + Z.of_nat (length p) <= 2^64)%Z.
  Hypothesis SB : (0 <= Sr /\ Sr + Z.of_nat (length bs) <= 2^64)%Z.
  Hypothesis SPR : (0 <= bv_unsigned sp < 2^64)%Z.
  Hypothesis LJ : length jd = dn.

  Notation W := [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (S0, S0 + Z.of_nat dn)]%Z.
  Notation SFW mm := (sfw S0 dn Sr l B ZSB ZK mm).
  Notation POST := (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp wend bufp bufsize mode CK S0 N B Sr l lo dn p bs jd m).
  Notation FRAME mm j8 := (rw_cells rsegs mm (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FILE mm wp wb := (rw_cells rsegs mm Fp (snfile z64 wend wp wb bufp bufsize mode CK)).
  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 l) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 Sr) x19 x20 (Z_to_bv 64 CK) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  (* [comment removed for export] *)
  #[using="LJ FB DB LP L7 L5 L4 L3 L2 L1 KH CEIL LO HB Hl ND N0 LEN Clg"] Lemma sn_from_6e0 : forall mm j8 (k : Z) (dlv : list byte) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
    dlv = firstn (Z.to_nat N) (p ++ bs) -> k = Z.of_nat (length dlv) ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 (S0 + k)); C8 (Z_to_bv 64 (N - k))] ->
    rw_cells rsegs mm S0 [CB dn (dlv ++ skipn (Z.to_nat k) jd)] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs -> SFW mm ->
    evt rsegs POST (ST 0xa1664 mm x1 x5 x6 x7 (Z_to_bv 64 (S0 + k)) x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hdlv Hk MI MU WM ST FR FL CKC DST BP BS SF.
    assert (KN : (0 <= k <= N)%Z). { subst k dlv. rewrite firstn_length. lia. }
    unfold snfile, z64, m1w in FL.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD. clear DST.
    pose proof (u8arr_store_ok rsegs _ _ _ k (Z_to_bv 64 (S0 + k)) DA ltac:(rewrite LD; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs. change (write_to_mem mm (Z_to_bv 64 (S0 + k)) [Z_to_bv 8 0]) with (write_to_mem mm (wa (S0 + k)) [Z_to_bv 8 0]).
    pose proof (u8arr_write rsegs _ _ _ k (Z_to_bv 8 0) DA ltac:(rewrite LD; lia)) as DA2. clear DA.
    store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LD in DST. clear DA2.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end). cbv zeta.
    rewrite <- Hdlv, <- Hk.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { unfold snfile, z64, m1w. assumption. }
    split. { exact CKC. }
    split. { rewrite upd_after_prefix in DST; [exact DST | lia | ].
             rewrite length_app, length_skipn in LD. lia. }
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ FB CB_ DB LP L7 L5 L4 L3 L2 L1 KH CEIL LO HB Hl ND N31 N0 LEN Clg"] Lemma sn_from_6c8 : forall mm j8 (k1 k2 : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    k1 = Z.min N (Z.of_nat (length p)) -> k2 = Z.min (N - k1) l -> (0 < k2)%Z ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 (S0 + k1)); C8 (Z_to_bv 64 (N - k1))] ->
    rw_cells rsegs mm S0 [CB dn (firstn (Z.to_nat k1) p ++ firstn (Z.to_nat k2) bs ++ skipn (Z.to_nat k1 + Z.to_nat k2) jd)] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs -> SFW mm ->
    evt rsegs POST (ST 0xa164c mm x1 x5 x6 x7 (Z_to_bv 64 (S0 + k1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 k2) (Z_to_bv 64 k1) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk1 Hk2 K2 MI MU WM ST FR FL CKC DST BP BS SF.
    pose proof (Z.le_min_l N (Z.of_nat (length p))). pose proof (Z.le_min_r N (Z.of_nat (length p))).
    pose proof (Z.le_min_l (N - k1) l). pose proof (Z.le_min_r (N - k1) l).
    assert (K1 : (0 <= k1)%Z) by (subst k1; apply Z.min_glb; lia).
    unfold snfile, z64, m1w in FL.
    zs. zs. zs. zs. zs. zs.
    replace (S0 + k1 + k2)%Z with (S0 + (k1 + k2))%Z by lia. replace (N - k1 - k2)%Z with (N - (k1 + k2))%Z by lia.
    eapply sn_from_6e0 with (dlv := firstn (Z.to_nat k1) p ++ firstn (Z.to_nat k2) bs); try eassumption.
    - (* [comment removed for export] *)
      destruct (Z.le_ge_cases (Z.of_nat (length p)) N) as [Hle|Hge].
      + assert (E1 : k1 = Z.of_nat (length p)) by lia. rewrite E1, Nat2Z.id, firstn_all.
        rewrite firstn_app. rewrite (firstn_all2 p) by lia. f_equal.
        assert (E2 : k2 = Z.min (N - Z.of_nat (length p)) (Z.of_nat (length bs))) by lia.
        destruct (Z.le_ge_cases (N - Z.of_nat (length p)) (Z.of_nat (length bs))).
        * f_equal. lia.
        * rewrite !firstn_all2 by lia. reflexivity.
      + assert (E1 : k1 = N) by lia. assert (k2 = 0%Z) by lia. lia.
    - rewrite length_app, !firstn_length, LEN. lia.
    - replace (S0 + (k1 + k2))%Z with (S0 + k1 + k2)%Z by lia. replace (N - (k1 + k2))%Z with (N - k1 - k2)%Z by lia. assumption.
    - replace (Z.to_nat (k1 + k2)) with (Z.to_nat k1 + Z.to_nat k2)%nat by lia. rewrite <- app_assoc. exact DST.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ SPR SB FB CB_ DB LP L7 L6 L5 L4 L3 L2 L1 KH CEIL LO HB Hl ND N31 N0 LEN Clg"] Lemma sn_from_6b0 : forall mm j8 (k1 : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    k1 = Z.min N (Z.of_nat (length p)) ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 (S0 + k1)); C8 (Z_to_bv 64 (N - k1))] ->
    rw_cells rsegs mm S0 [CB dn (firstn (Z.to_nat k1) p ++ skipn (Z.to_nat k1) jd)] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs -> SFW mm ->
    evt rsegs POST (ST 0xa1634 mm x1 x5 x6 x7 (Z_to_bv 64 (S0 + k1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (N - k1)) (Z_to_bv 64 k1) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk1 MI MU WM ST FR FL CKC DST BP BS SF.
    pose proof (Z.le_min_l N (Z.of_nat (length p))). pose proof (Z.le_min_r N (Z.of_nat (length p))).
    assert (K1 : (0 <= k1)%Z) by (subst k1; apply Z.min_glb; lia).
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD. pose proof alloc_ceiling_val as CV.
    zs. brf K1'.
    - (* [comment removed for export] *)
      zs. brf K2.
      + (* [comment removed for export] *)
        replace (S0 + k1)%Z with (S0 + (k1 + 0))%Z by lia. 
        eapply sn_from_6e0 with (dlv := firstn (Z.to_nat k1) p); try eassumption.
        * assert (E1 : k1 = N) by lia. rewrite E1. rewrite firstn_app_le by lia. reflexivity.
        * rewrite firstn_length. lia.
        * replace (S0 + (k1 + 0))%Z with (S0 + k1)%Z by lia. replace (N - (k1 + 0))%Z with (N - k1)%Z by lia. exact CKC.
        * replace (Z.to_nat (k1 + 0)) with (Z.to_nat k1) by lia. exact DST.
      + (* [comment removed for export] *)
        (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ (Z.to_nat k1) (Z.to_nat (N - k1)) DST ltac:(lia))) as dR_3; dand3 dR_3 as DA DB2 DC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ (Z.to_nat k1) (Z.to_nat (N - k1)) DST ltac:(lia)) as (DA & DB2 & DC) ]). clear DST.
        rewrite firstn_app_le, firstn_firstn, Nat.min_id in DA by (rewrite firstn_length; lia).
        zs. zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          eapply evt_cut; [ eapply memcpy_callv with (src := firstn (Z.to_nat (N - k1)) bs) (lo := lo) | post_call_icpt rsegs mq ] end.
        { eapply bytes_at_prefix. rewrite firstn_skipn. exact BS. }
        { rewrite firstn_length, LEN. lia. }
        { eapply rwc_eq; [exact DB2 | lia]. }
        { lia. } { lia. } { lia. } { lia. } { exact MI. }
        { open_sfw SF. exact CE. } { rewrite ?unsigned_lit by lia; exact ST. } { rewrite ?unsigned_lit by lia; lia. } { exact CEIL. }
        { rewrite ?unsigned_lit by lia; lia. } { rewrite ?unsigned_lit by lia; lia. }
        { open_sfw SF. right. split; [destruct RS as [RS|RS]; [exfalso; lia| eapply range_ok_sub; [exact RS| lia| lia| lia]]
                                    | eapply range_ok_sub; [exact RD| lia| lia| lia]]. }
        match goal with Hb : rw_cells _ ?mq (S0 + k1)%Z _, MIq : mem_inv _ ?mq |- _ =>
          pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ DA ltac:(eapply rwc_eq; [exact Hb| lia]) DC) as DST; clear DA Hb DC;
          rename MIq into MI2 end.
        replace (Z.to_nat k1 + Z.to_nat (N - k1) + (dn - Z.to_nat k1 - Z.to_nat (N - k1)))%nat with dn in DST by lia.
        eapply (sn_from_6c8 _ _ k1 (N - k1)); try eassumption; try lia.
        rewrite skipn_app_exact in DST by (rewrite firstn_length; lia). exact DST.
      - (* [comment removed for export] *)
        zs. zs. brf K2.
        + (* [comment removed for export] *)
          replace (S0 + k1)%Z with (S0 + (k1 + 0))%Z by lia.
          eapply sn_from_6e0 with (dlv := firstn (Z.to_nat k1) p); try eassumption.
          * assert (E1 : bs = []) by (destruct bs; [reflexivity| cbn in LEN; lia]). rewrite E1, app_nil_r.
            destruct (Z.le_ge_cases (Z.of_nat (length p)) N).
            -- assert (E2 : k1 = Z.of_nat (length p)) by lia. rewrite E2, Nat2Z.id, firstn_all, firstn_all2 by lia. reflexivity.
            -- f_equal. lia.
          * rewrite firstn_length. lia.
          * replace (S0 + (k1 + 0))%Z with (S0 + k1)%Z by lia. replace (N - (k1 + 0))%Z with (N - k1)%Z by lia. exact CKC.
          * replace (Z.to_nat (k1 + 0)) with (Z.to_nat k1) by lia. exact DST.
        + (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ (Z.to_nat k1) (Z.to_nat l) DST ltac:(lia))) as dR_4; dand3 dR_4 as DA DB2 DC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ (Z.to_nat k1) (Z.to_nat l) DST ltac:(lia)) as (DA & DB2 & DC) ]). clear DST.
          rewrite firstn_app_le, firstn_firstn, Nat.min_id in DA by (rewrite firstn_length; lia).
          zs. zs. zs.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
            eapply evt_cut; [ eapply memcpy_callv with (src := bs) (lo := lo) | post_call_icpt rsegs mq ] end.
          { exact BS. }
          { exact LEN. }
          { eapply rwc_eq; [exact DB2 | lia]. }
          { lia. } { lia. } { lia. } { lia. } { exact MI. }
          { open_sfw SF. exact CE. } { rewrite ?unsigned_lit by lia; exact ST. } { rewrite ?unsigned_lit by lia; lia. } { exact CEIL. }
        { rewrite ?unsigned_lit by lia; lia. } { rewrite ?unsigned_lit by lia; lia. }
          { open_sfw SF. right. split; [destruct RS as [RS|RS]; [exfalso; lia| eapply range_ok_sub; [exact RS| lia| lia| lia]]
                                      | eapply range_ok_sub; [exact RD| lia| lia| lia]]. }
          match goal with Hb : rw_cells _ ?mq (S0 + k1)%Z _, MIq : mem_inv _ ?mq |- _ =>
            pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ DA ltac:(eapply rwc_eq; [exact Hb| lia]) DC) as DST; clear DA Hb DC;
            rename MIq into MI2 end.
          replace (Z.to_nat k1 + Z.to_nat l + (dn - Z.to_nat k1 - Z.to_nat l))%nat with dn in DST by lia.
          eapply (sn_from_6c8 _ _ k1 l); try eassumption; try lia.
          rewrite skipn_app_exact in DST by (rewrite firstn_length; lia).
          rewrite <- LEN, firstn_all. rewrite LEN. exact DST.
  Qed.

  (* [comment removed for export] *)
  #[using="LJ SPR SB BB FB CB_ DB LP L7 L6 L5 L4 L3 L2 L1 KH CEIL LO HB Hl ND N31 N0 LEN Clg"] Lemma sn_from_688 : forall mm j8 (k1 : Z) x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    k1 = Z.min N (Z.of_nat (length p)) ->
    mem_inv rsegs mm -> munch W m mm -> wmono rsegs m mm ->
    stk rsegs mm lo (bv_unsigned sp + -64) -> FRAME mm j8 ->
    FILE mm (B + Z.of_nat (length p)) B ->
    rw_cells rsegs mm CK [C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 N)] ->
    rw_cells rsegs mm S0 [CB dn jd] ->
    bytes_at rsegs mm B p -> bytes_at rsegs mm Sr bs -> SFW mm ->
    evt rsegs POST (ST 0xa160c mm ra x5 x6 x7 x10 (Z_to_bv 64 B) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 k1) x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hk1 MI MU WM ST FR FL CKC DST BP BS SF.
    pose proof (Z.le_min_l N (Z.of_nat (length p))). pose proof (Z.le_min_r N (Z.of_nat (length p))).
    assert (K1 : (0 <= k1)%Z) by (subst k1; apply Z.min_glb; lia). pose proof alloc_ceiling_val as CV.
    zs. zs. brf K0.
    - (* [comment removed for export] *)
      rewrite K0. replace (Z_to_bv 64 S0) with (Z_to_bv 64 (S0 + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 N) with (Z_to_bv 64 (N - 0)) by (f_equal; lia).
      eapply (sn_from_6b0 _ _ 0%Z); try eassumption; try lia.
      rewrite Z.add_0_r, Z.sub_0_r. exact CKC.
    - (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ 0%nat (Z.to_nat k1) DST ltac:(lia))) as dR_5; dand3 dR_5 as DA DB2 DC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ 0%nat (Z.to_nat k1) DST ltac:(lia)) as (DA & DB2 & DC) ]). clear DST.
      cbn [firstn skipn] in DB2. rewrite Z.add_0_r in DB2.
      zs. zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        eapply evt_cut; [ eapply memcpy_callv with (src := firstn (Z.to_nat k1) p) (lo := lo) | post_call_icpt rsegs mq ] end.
      { eapply bytes_at_prefix. rewrite firstn_skipn. exact BP. }
      { rewrite firstn_length. lia. }
      { exact DB2. }
      { lia. } { lia. } { lia. } { lia. } { exact MI. }
      { open_sfw SF. exact CE. } { rewrite ?unsigned_lit by lia; exact ST. } { rewrite ?unsigned_lit by lia; lia. } { exact CEIL. }
        { rewrite ?unsigned_lit by lia; lia. } { rewrite ?unsigned_lit by lia; lia. }
      { open_sfw SF. right. split; [ eapply (range_ok_of_zeros _ ZSB ZK B (B + 80)); [exact ZS| exact ZB| lia| lia| lia]
                                    | eapply range_ok_sub; [exact RD| lia| lia| lia]]. }
      unfold snfile, z64, m1w in FL.
      zs. zs. zs. zs. zs. zs.
      match goal with Hb : rw_cells _ ?mq S0 [CB (Z.to_nat k1) _], MIq : mem_inv _ ?mq |- _ =>
        pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ DA ltac:(eapply rwc_eq; [exact Hb| cbn; lia]) ltac:(eapply rwc_eq; [exact DC | cbn; lia])) as DST; clear DA Hb DC;
        rename MIq into MI2 end.
      cbn [firstn app Nat.add] in DST. rewrite Nat.sub_0_r in DST.
      replace (Z.to_nat k1 + (dn - Z.to_nat k1))%nat with dn in DST by lia.
      eapply (sn_from_6b0 _ _ k1); try eassumption; try lia.
  Qed.

  #[using="LJ SPR SB BB FB CB_ DB LP L7 L6 L5 L4 L3 L2 L1 KH CEIL LO HB Hl ND N31 N0 LEN Clg"] Lemma sn_write_body : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m Fp (snfile z64 wend (B + Z.of_nat (length p)) B bufp bufsize mode CK) ->
    rw_cells rsegs m CK [C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 N)] ->
    rw_cells rsegs m S0 [CB dn jd] ->
    bytes_at rsegs m B p -> bytes_at rsegs m Sr bs -> mem_inv rsegs m -> SFW m ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 Sr) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa15c0) fc None m (seg_rom rsegs)).
  Proof.
    intros until t6. intros ST FL CKC DST BP BS MI SF.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold snfile, z64, m1w in FL.
    carve_frame 64%nat ST.
    do 15 zs.
    zs. replace (B + Z.of_nat (length p) - B)%Z with (Z.of_nat (length p)) by lia.
    zs. zs. brf K1.
    - eapply (sn_from_688 _ _ N); try eassumption; try lia.
    - zs. eapply (sn_from_688 _ _ (Z.of_nat (length p))); try eassumption; try lia.
  Qed.
End SnWrite.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma sn_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Fp wend bufp bufsize : Z) (mode : word) (CK S0 N B Sr l lo : Z) (dn : nat) (p bs jd : list byte) (ZSB : Z) (ZK : nat),
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 Sr -> a2 = Z_to_bv 64 l ->
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m Fp (snfile z64 wend (B + Z.of_nat (length p)) B bufp bufsize mode CK) ->
  rw_cells rsegs m CK [C8 (Z_to_bv 64 S0); C8 (Z_to_bv 64 N)] ->
  rw_cells rsegs m S0 [CB dn jd] ->
  bytes_at rsegs m B p -> bytes_at rsegs m Sr bs -> mem_inv rsegs m ->
  sfw S0 dn Sr l B ZSB ZK m -> (alloc_ceiling <= lo)%Z -> dst_zone S0 (Z.of_nat dn) ->
  length bs = Z.to_nat l -> (0 <= N)%Z -> (N < 2^31)%Z -> (N + 1 <= Z.of_nat dn)%Z -> (0 <= l < 2^63)%Z ->
  (Z.of_nat (length p) <= 80)%Z -> (0 <= bufp < 2^64)%Z ->
  (0 <= lo <= bv_unsigned sp - 2304)%Z ->
  (S0 + Z.of_nat dn <= lo)%Z -> (bv_unsigned sp <= B)%Z -> (B + 80 <= Fp)%Z -> (CK = Fp + 232)%Z -> (Fp + 248 <= 2^64)%Z ->
  (Sr + l <= B)%Z -> (~ (lo < Sr + l /\ Sr < bv_unsigned sp))%Z -> (~ (S0 < Sr + l /\ Sr < S0 + Z.of_nat dn))%Z ->
  (Fp + 248 <= 2^63)%Z ->
  evt rsegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp wend bufp bufsize mode CK S0 N B Sr l lo dn p bs jd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa15c0) fc None m (seg_rom rsegs)).
Proof.
  intros until ZK. intros -> -> -> ST FL CKC DST BP BS MI SF CEIL KH LEN N0 N31 ND Hl LP Hbuf LO L1 L2 L3 L4 F64 L5 L6 L7 F63.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB. rewrite Nat.add_0_r in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ FL) as FB. rewrite snfile_size in FB.
  pose proof (bytes_at_bound _ _ _ _ BP) as BB. pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LJ.
  eapply sn_write_body; try eassumption; try lia.
Qed.

End CEIL.
End RA_sh6p.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_mqq1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_f93z.RA_sh6p.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcp2qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

(* [comment removed for export] *)
Definition sfx (D : Z) (n : nat) (Sr l B SB : Z) (K : nat) (m : word -> option byte) : Prop :=
     asan_memcpy_cells m /\ range_ok m D (Z.of_nat n) /\ (l = 0%Z \/ range_ok m Sr l)
  /\ bytes_at rsegs m SB (zeros K) /\ zsh_bounds SB K B (B + 80)
  /\ (2147446784 <= SB)%Z.   (* [comment removed for export] *)
Lemma lowP_sfx : forall D n Sr l B SB K, (0 <= l)%Z -> lowP (sfx D n Sr l B SB K).
Proof. intros. apply lowP_sfw. assumption. Qed.
Lemma sfx_sfw : forall D n Sr l B SB K m k, sfx D n Sr l B SB K m -> (k < n)%nat ->
  sfw (D + Z.of_nat k) (n - k) Sr l B SB K m.
Proof.
  (intros D n Sr l B SB K m k; (first [ intro dR_10; dand6 dR_10 as C1 R1 R2 ZS ZB SBL | intros (C1 & R1 & R2 & ZS & ZB & SBL) ]); intros Hk). split; [exact C1|]. split; [| split; [exact R2| split; [exact ZS| exact (conj ZB SBL)]]].
  eapply range_ok_sub; [exact R1| lia| lia| lia].
Qed.
(* [comment removed for export] *)
Lemma sf2_sfx : forall A la D n HS hs SB K q m Sr l Bq,
  sf2 A la D n HS hs SB K (q - 544) (q + 96) m ->
  (l = 0%Z \/ range_ok m Sr l) -> Bq = (q + 16)%Z ->
  sfx D n Sr l Bq SB K m.
Proof.
  (intros A la D n HS hs SB K q m Sr l Bq; (first [ intro dR_11; dand8 dR_11 as C1 C2 R1 R2 H5 ZS ZB SBL | intros (C1 & C2 & R1 & R2 & H5 & ZS & ZB & SBL) ]); intros RS ->).
  split; [exact C1|]. split; [exact R2|]. split; [exact RS|]. split; [exact ZS|]. split; [| exact SBL].
  eapply zsh_bounds_sub; [exact ZB| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Ltac low_lemma_pf P :=
  lazymatch P with
  | sf2 ?A ?la ?D ?n ?HS ?hs ?SB ?K ?zlo ?zhi => constr:(lowP_sf2 A la D n HS hs SB K zlo zhi ltac:(lia))
  | sfx ?D ?n ?Sr ?l ?B ?SB ?K => constr:(lowP_sfx D n Sr l B SB K ltac:(lia))
  | sfw ?S0 ?dn ?Sr ?l ?B ?SB ?K => constr:(lowP_sfw S0 dn Sr l B SB K ltac:(lia))
  | _ => low_lemma_base P
  end.
Local Ltac low_lemma P ::= low_lemma_pf P.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= relow_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= relow_all W m m' MU.
Ltac open_sfx H := let a := fresh "CE" in let b := fresh "RD" in let c := fresh "RS" in let d := fresh "ZS" in let e := fresh "ZB" in
  let f := fresh "SBL" in (first [ pose proof (H) as dR_1; dex5 dR_1 as a b c d e; rename dR_1 into f | pose proof (H) as dR_1; dand6 dR_1 as a b c d e f | pose proof H as (a & b & c & d & e & f) ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sn_layout {Clg : Ceiling} (sp : word) (lo Fp B D : Z) (n : nat) (Sr l : Z) : Prop :=   (* [comment removed for export] *)
  (0 <= lo <= bv_unsigned sp - 2304)%Z /\ (D + Z.of_nat n <= lo)%Z /\ (bv_unsigned sp <= B)%Z /\ (B + 80 <= Fp)%Z
  /\ (Fp + 248 <= 2^63)%Z /\ (Sr + l <= B)%Z /\ (~ (lo < Sr + l /\ Sr < bv_unsigned sp))%Z
  /\ (~ (D < Sr + l /\ Sr < D + Z.of_nat n))%Z /\ (0 <= Sr)%Z /\ (0 <= D)%Z
  /\ (alloc_ceiling <= lo)%Z /\ dst_zone D (Z.of_nat n) /\ (Z.of_nat n <= 2^31)%Z.      (* [comment removed for export] *)

Definition sn_write_sink_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ sink Fp B D n m' mode (w ++ p ++ bs) []
    /\ bytes_at rsegs m' Sr bs.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma sn_write_sink : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z) (ZSB : Z) (ZK : nat),
  a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 Sr -> a2 = Z_to_bv 64 l ->
  stk rsegs m lo (bv_unsigned sp) ->
  sink Fp B D n m mode w p ->
  bytes_at rsegs m Sr bs -> length bs = Z.to_nat l -> (0 <= l < 2^63)%Z ->
  sn_layout sp lo Fp B D n Sr l ->
  mem_inv rsegs m -> sfx D n Sr l B ZSB ZK m ->
  evt rsegs (sn_write_sink_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B D n mode w p bs Sr l lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa15c0) fc None m (seg_rom rsegs)).
Proof.
  intros until ZK. intros Ha0 Ha1 Ha2 ST SNK BS LEN Hl LAY MI SF.
  (first [ dex2 SNK as jb jd; dand5 SNK as FL CKC BUF DST N1 | dand7 SNK as jb jd FL CKC BUF DST N1 | destruct SNK as (jb & jd & FL & CKC & BUF & DST & N1) ]).
  (first [ dand13 LAY as LO L1 L2 L3 F63 L5 L6 L7 SR0 D0 GT KH N31 | destruct LAY as (LO & L1 & L2 & L3 & F63 & L5 & L6 & L7 & SR0 & D0 & GT & KH & N31) ]). pose proof (Z.le_trans _ _ _ globals_top_ceiling GT) as GT'; unfold GLOBALS_TOP in GT'.
  pose proof alloc_ceiling_val as CV.
  pose proof (dl_length n w) as DLL.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LD. rewrite length_app in LD. cbn [length] in LD.
  pose proof (rw_CB_length _ _ _ _ _ BUF) as LB. rewrite length_app in LB.
  (* [comment removed for export] *)
  (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ (length (dl n w)) (n - length (dl n w)) DST ltac:(lia))) as dR_4; dand3 dR_4 as DA DB DC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ (length (dl n w)) (n - length (dl n w)) DST ltac:(lia)) as (DA & DB & DC) ]). clear DC.
  rewrite firstn_app_le, firstn_all in DA by lia.
  rewrite skipn_app, skipn_all, Nat.sub_diag in DB. cbn [skipn app] in DB.
  rewrite firstn_all2 in DB by (cbn; lia).
  eapply evt_mono.
  { eapply (sn_write_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              Fp (B + 80) B 80 mode (Fp + 232) (D + Z.of_nat (length (dl n w))) (Z.of_nat n - 1 - Z.of_nat (length (dl n w))) B Sr l lo
              (n - length (dl n w))%nat p bs (Z_to_bv 8 0 :: jd) ZSB ZK);
      try eassumption; try reflexivity; try lia; try (eapply dst_zone_sub; [exact KH| lia| lia]).
    - eapply bytes_at_prefix. pose proof (bytes_at_of_rw_cells _ _ _ _ BUF) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
    - apply sfx_sfw; [exact SF| lia]. }
  cbv beta. intros ms' P. unfold sn_write_post in P. cbv zeta in P.
  (first [ dex15 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m'; dand10 P as -> MU WM MI' ST' FL' CKC' DST' BP' BS' | dand25 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MU WM MI' ST' FL' CKC' DST' BP' BS' | destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & FL' & CKC' & DST' & BP' & BS') ]).
  unfold sn_write_sink_post. hot_eexists_all.
  split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros. lia. }
  split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [|exact BS'].
  (* [comment removed for export] *)
  set (k := Z.of_nat (length (firstn (Z.to_nat (Z.of_nat n - 1 - Z.of_nat (length (dl n w)))) (p ++ bs)))) in *.
  assert (Hdl : dl n (w ++ p ++ bs) = dl n w ++ firstn (Z.to_nat (Z.of_nat n - 1 - Z.of_nat (length (dl n w)))) (p ++ bs)).
  { rewrite dl_app. f_equal. f_equal. lia. }
  assert (Hk : length (dl n (w ++ p ++ bs)) = (length (dl n w) + Z.to_nat k)%nat).
  { rewrite Hdl, length_app. subst k. rewrite Nat2Z.id. reflexivity. }
  pose proof (rw_cells_transport rsegs _ _ _ _ _ BUF MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; lia)) as BUF'.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ DA MU WM ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; lia)) as DA'.
  first [ hotw_ex2 (p ++ jb) (skipn (Z.to_nat k) jd) | exists (p ++ jb), (skipn (Z.to_nat k) jd) ].
  split. { replace (B + Z.of_nat (@length byte []))%Z with B by (cbn; lia). exact FL'. }
  split. { rewrite Hk, Nat2Z.inj_add, Z2Nat.id by lia.
           replace (D + (Z.of_nat (length (dl n w)) + k))%Z with (D + Z.of_nat (length (dl n w)) + k)%Z by lia.
           replace (Z.of_nat n - 1 - (Z.of_nat (length (dl n w)) + k))%Z with (Z.of_nat n - 1 - Z.of_nat (length (dl n w)) - k)%Z by lia.
           exact CKC'. }
  split. { cbn [app]. exact BUF'. }
  split.
  { pose proof (rw_CB_length _ _ _ _ _ DST') as LD'.
    lazymatch type of DST' with rw_cells _ _ _ [CB _ ?l2] =>
    assert (J : rw_cells rsegs m' D ([] ++ [CB (length (dl n w)) (dl n w); CB (n - length (dl n w)) l2] ++ []));
    [ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact DA'|]; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact DST' |] end.
    apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite app_nil_r, Nat.add_0_r in J.
    replace (length (dl n w) + (n - length (dl n w)))%nat with n in J by lia.
    rewrite Hdl, <- app_assoc. cbn [app].
    change (skipn (S (Z.to_nat k)) (Z_to_bv 8 0 :: jd)) with (skipn (Z.to_nat k) jd) in J. exact J. }
  exact N1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n); (B, B + 80)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ sink Fp B D n m' mode (fst (fwx w p bs)) (snd (fwx w p bs))
    /\ bytes_at rsegs m' Sr bs.

Lemma fwritex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Fp B D : Z) (n : nat) (mode : word) (w p bs : list byte) (Sr l lo : Z) (ZSB : Z) (ZK : nat),
  a0 = Z_to_bv 64 Sr -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  stk rsegs m lo (bv_unsigned sp) ->
  sink Fp B D n m mode w p ->
  bytes_at rsegs m Sr bs -> length bs = Z.to_nat l -> (0 <= l < 2^63)%Z ->
  sn_layout sp lo Fp B D n Sr l ->
  mem_inv rsegs m -> sfx D n Sr l B ZSB ZK m ->
  evt rsegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B D n mode w p bs Sr l lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9e008) fc None m (seg_rom rsegs)).
Proof.
  intros until ZK. intros -> -> -> ST SNK BS LEN Hl LAY MI SF.
  (first [ dex2 SNK as jb jd; dand5 SNK as FL CKC BUF DST N1 | dand7 SNK as jb jd FL CKC BUF DST N1 | destruct SNK as (jb & jd & FL & CKC & BUF & DST & N1) ]).
  pose proof LAY as LAY'. (first [ dand13 LAY as LO L1 L2 L3 F63 L5 L6 L7 SR0 D0 GT KH N31 | destruct LAY as (LO & L1 & L2 & L3 & F63 & L5 & L6 & L7 & SR0 & D0 & GT & KH & N31) ]). pose proof (Z.le_trans _ _ _ globals_top_ceiling GT) as GT'; unfold GLOBALS_TOP in GT'.
  pose proof alloc_ceiling_val as CV.
  pose proof (rw_CB_length _ _ _ _ _ BUF) as LB. rewrite length_app in LB.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 248); (D, D + Z.of_nat n); (B, B + 80)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold snfile, z64, m1w, SN_WRITE in FL.
  carve_frame 64%nat ST.
  do 12 zs.
  zs. brf K0. { exfalso. lia. }
  zs. zs. replace (B + 80 - (B + Z.of_nat (length p)))%Z with (80 - Z.of_nat (length p))%Z by lia.
  zs. brf K1.
  - (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    (first [ pose proof ((rw_cells_CB_split3 rsegs _ _ _ _ (length p) (Z.to_nat l) BUF ltac:(lia))) as dR_8; dand3 dR_8 as BA BB BC | destruct (rw_cells_CB_split3 rsegs _ _ _ _ (length p) (Z.to_nat l) BUF ltac:(lia)) as (BA & BB & BC) ]). clear BUF.
    rewrite firstn_app_le, firstn_all in BA by lia.
    zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut; [ eapply memcpy_callv with (src := bs) (lo := lo) | post_call_icpt rsegs mq ] end.
    { exact BS. } { exact LEN. } { eapply rwc_eq; [exact BB | lia]. }
    { lia. } { lia. } { lia. } { lia. } { assumption. }
    { open_sfx SF. exact CE. } { rewrite ?unsigned_lit by lia; eassumption. } { rewrite ?unsigned_lit by lia; lia. } { exact GT. }
    { rewrite ?unsigned_lit by lia; lia. } { rewrite ?unsigned_lit by lia; lia. }
    { open_sfx SF. destruct (Z.eq_dec l 0) as [E0|NE]; [left; exact E0| right].
      split; [destruct RS as [RS|RS]; [exfalso; lia| exact RS]
            | eapply (range_ok_of_zeros _ ZSB ZK B (B + 80)); [exact ZS| exact ZB| lia| lia| lia]]. }
    match goal with Hb : rw_cells _ ?mq (B + Z.of_nat (length p))%Z _, MIq : mem_inv _ ?mq |- _ =>
      pose proof (rw_cells_CB_join3 rsegs _ _ _ _ _ _ _ _ BA ltac:(eapply rwc_eq; [exact Hb| lia]) ltac:(eapply rwc_eq; [exact BC| lia])) as BUF; clear BA Hb BC;
      rename MIq into MI2 end.
    match goal with H : stk rsegs _ lo _ |- _ => rename H into ST end.
    replace (length p + Z.to_nat l + (80 - length p - Z.to_nat l))%nat with 80%nat in BUF by lia.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold fwritex_post. hot_eexists_all.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [| assumption].
    unfold fwx. replace (Z.of_nat (length bs) <=? 80 - Z.of_nat (length p))%Z with true by (symmetry; apply Z.leb_le; lia). cbn [fst snd].
    first [ hotw_ex2 (skipn (Z.to_nat l) jb) jd | exists (skipn (Z.to_nat l) jb), jd ].
    split. { unfold snfile, z64, m1w, SN_WRITE. rewrite length_app, Nat2Z.inj_add, LEN, Z2Nat.id, Z.add_assoc by lia. assumption. }
    split; [assumption|]. split.
    { rewrite <- app_assoc. rewrite skipn_app_exact2 in BUF by lia. exact BUF. }
    split; assumption.
  - (* [comment removed for export] *)
    zs. zs. zs. zs. do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    eapply evt_cut; [ eapply (sn_write_sink ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mq Fp B D n mode w p bs Sr l lo ZSB ZK);
                      try reflexivity; try eassumption | ] end.
    { first [ hotw_ex2 jb jd | exists jb, jd ]. refine (conj _ (conj _ (conj _ (conj _ N1)))); [unfold snfile, z64, m1w, SN_WRITE; assumption | assumption | assumption | assumption]. }
    cbv beta. intros ms' P. unfold sn_write_sink_post in P.
    (first [ dex15 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m'; dand7 P as -> MU' WM' MI' ST' SNK' BS' | dand22 P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MU' WM' MI' ST' SNK' BS' | destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU' & WM' & MI' & ST' & SNK' & BS') ]).
    apply evt_done. unfold fwritex_post. hot_eexists_all.
    split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]. intros. lia. }
    split. { eapply wmono_trans; [exact WM| exact WM']. }
    split; [exact MI'|]. split; [exact ST'|].
    split; [| exact BS'].
    unfold fwx. replace (Z.of_nat (length bs) <=? 80 - Z.of_nat (length p))%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    exact SNK'.
Qed.

End CEIL.
