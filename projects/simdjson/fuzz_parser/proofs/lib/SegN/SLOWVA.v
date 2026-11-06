(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC SegLin.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjVCPre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SWARZ SLOWG NRMG SLOWV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module SNVA.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma rr1s : forall segs m E a k v, sc_denot segs m E (SCReadBase (SA a k) 1 true (EVar v)) ->
  exists b, SNG.bat segs m (u (adenot E (SA a k))) b /\ 0 <= b < 256 /\ u (ev E v) mod 256 = b.
Proof.
  intros segs m E a k v (bs & Hr & Hv). cbn [edenot] in Hv.
  pose proof (rdn_length segs m 1 _ bs Hr) as Hl. destruct bs as [|c [|c' r]]; try discriminate Hl.
  pose proof (SV.rd1_rdn segs m _ c Hr) as Hc.
  pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. cbn in R.
  exists (u c). split; [exists c; split; [unfold SNG.rb; rewrite Z_to_bv_bv_unsigned; exact Hc | reflexivity]|].
  split; [lia|].
  rewrite <- Hv. cbn [extz bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold bv_swrap, bv_half_modulus, bv_wrap.
  change (bv_modulus (8 * N.of_nat 1)) with 256. change (256 / 2) with 128.
  rewrite <- (Znumtheory.Zmod_div_mod 256 (2 ^ 64)) by (lia || (exists (2 ^ 56); lia)).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (u c + 128 - 128) with (u c) by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma mod64_32 : forall S c, (S mod 2 ^ 64 + c) mod 2 ^ 32 = (S + c) mod 2 ^ 32.
Proof.
  intros S c. rewrite Zplus_mod, (Zplus_mod S c). f_equal. f_equal.
  rewrite <- (Znumtheory.Zmod_div_mod (2 ^ 32) (2 ^ 64) S) by (lia || (exists (2 ^ 32); lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swar4_bridge_sx : forall v0 v1 v2 b3 V3 S A B,
  S = v0 + 256 * v1 + 65536 * v2 + 16777216 * V3 ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= b3 < 256 -> V3 mod 256 = b3 -> 0 <= A -> 0 <= B ->
  A mod 2 ^ 32 = (S mod 2 ^ 64 + 1179010630) mod 2 ^ 32 -> B mod 2 ^ 32 = (S mod 2 ^ 64 + 18446744072901087184) mod 2 ^ 32 ->
  Z.land (Z.lor A B) (18446744071570489472 mod 2 ^ 64) = 0 ->
  48 <= v0 <= 57 /\ 48 <= v1 <= 57 /\ 48 <= v2 <= 57 /\ 48 <= b3 <= 57.
Proof.
  intros v0 v1 v2 b3 V3 S A B HS H0 H1 H2 H3 HV HA HB EA EB HC.
  rewrite mod64_32 in EA, EB.
  apply (SNV.swar4_bridge_ext v0 v1 v2 b3 (V3 / 256) S A B); [ | exact H0 | exact H1 | exact H2 | exact H3 | exact HA | exact HB | exact EA | exact EB | exact HC].
  rewrite HS, <- HV. pose proof (Z.div_mod V3 256 ltac:(lia)) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma land_m33_all : forallb (fun x => Z.eqb (Z.land x (18446744073709551583 mod 2 ^ 64)) (x - 32 * ((x / 32) mod 2))) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma land_m33 : forall x, 0 <= x < 256 -> Z.land x (18446744073709551583 mod 2 ^ 64) = x - 32 * ((x / 32) mod 2).
Proof.
  intros x Hx. pose proof (proj1 (forallb_forall _ _) land_m33_all x) as H.
  apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.
Lemma land_m33' : forall x, 0 <= x < 256 -> Z.land x (-33 mod 2 ^ 64) = x - 32 * ((x / 32) mod 2).
Proof. intros x Hx. change (-33 mod 2 ^ 64) with (18446744073709551583 mod 2 ^ 64). exact (land_m33 x Hx). Qed.

(* [comment removed for export] *)
Lemma nzd_intro0 : forall segs m ip il z k fp, 0 <= ip -> 0 <= il -> SNG.digs segs m ip il ->
  ip <= z -> SNG.zdot segs m ip (z - ip) -> SNG.cnt0 segs m ip (Z.to_nat (z - ip)) = k ->
  ((exists b, SNG.bat segs m z b /\ b <> 48 /\ b <> 46) \/ (ip + il <= z /\ fp + 0 <= z)) -> k + 20 <= il + 0 ->
  (exists j, 0 <= j < il /\ exists b, SNG.bat segs m (ip + j) b /\ 49 <= b <= 57) \/
  (exists j, 0 <= j < 0 /\ exists b, SNG.bat segs m (fp + j) b /\ 49 <= b <= 57).
Proof.
  intros segs m ip il z k fp H1 H2 HD Hz HZ HK HS HC.
  exact (SNG.nzd_intro' segs m ip il fp 0 z k H1 H2 ltac:(lia) HD ltac:(intros j Hj; lia) (or_introl eq_refl) Hz HZ HK HS HC).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sna_trim :=
  repeat match goal with
  | H : context [Z.land _ _] |- _ => clear H
  | H : context [Z.lor _ _] |- _ => clear H
  | H : context [_ mod 2 ^ 32] |- _ => clear H
  | H : SNG.bat _ _ _ _ |- _ => clear H
  | H : SNG.digs _ _ _ _ |- _ => clear H
  | H : SNG.zdot _ _ _ _ |- _ => clear H
  | H : _ -> SNG.zeros _ _ _ _ |- _ => clear H
  | H : sc_denot _ _ _ _ |- _ => clear H
  | H : know_ok _ _ _ _ |- _ => clear H
  end.
Ltac sna_lia := solve [ lia | (sna_trim; lia) ].
Ltac sna_lia_t := solve [ (sna_trim; lia) | lia ].
Ltac sna_lia_o := solve [ (sna_trim; lia) ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sna_ext :=
  repeat match goal with
  | H : context [bv_unsigned (edenot ?E (EExt false 0 1 (EVar ?v)))] |- _ => rewrite (SNV.u_ext1_v E v ltac:(sna_lia_t)) in H
  | |- context [bv_unsigned (edenot ?E (EExt false 0 1 (EVar ?v)))] => rewrite (SNV.u_ext1_v E v ltac:(sna_lia_t))
  end.
Ltac sna_land :=
  repeat match goal with
  | H : context [Z.land ?x (18446744073709551583 mod 2 ^ 64)] |- _ => rewrite (land_m33 x ltac:(sna_lia_t)) in H
  | |- context [Z.land ?x (18446744073709551583 mod 2 ^ 64)] => rewrite (land_m33 x ltac:(sna_lia_t))
  | H : context [Z.land ?x (-33 mod 2 ^ 64)] |- _ => rewrite (land_m33' x ltac:(sna_lia_t)) in H
  | |- context [Z.land ?x (-33 mod 2 ^ 64)] => rewrite (land_m33' x ltac:(sna_lia_t))
  end.
Ltac sna_bats :=
  repeat match goal with
  | B : SNG.bat _ _ ((?x + 0) mod 2 ^ 64) _ |- _ => rewrite Z.add_0_r in B
  | B : SNG.bat _ _ ?a _ |- _ =>
      match a with context [?x mod 2 ^ 64] =>
        lazymatch x with context [_ mod _] => fail | _ => idtac end;
        rewrite (Z.mod_small x (2 ^ 64)) in B by sna_lia_o end
  end.
Ltac sna_hmods :=
  repeat match goal with
  | H : SNG.digs _ _ ?a (?x mod 2 ^ 64) |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by sna_lia_t
  | H : SNG.digs _ _ (?x mod 2 ^ 64) _ |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by sna_lia_t
  | H : SNG.zdot _ _ ?a (?x mod 2 ^ 64) |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by sna_lia_t
  | H : SNG.zdot _ _ (?x mod 2 ^ 64) _ |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by sna_lia_t
  | H : _ -> SNG.zeros _ _ ?a (?x mod 2 ^ 64) |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by sna_lia_t
  | H : _ -> SNG.zeros _ _ (?x mod 2 ^ 64) _ |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by sna_lia_t
  end.
Ltac sna_gmods := repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by sna_lia_t end.

(* [comment removed for export] *)
Ltac sna_sreads :=
  repeat match goal with
  | P : sc_denot ?segs ?m ?E (SCReadBase (SA ?a ?k) 1 true (EVar ?v)) |- _ =>
      let b := fresh "sb" in let B := fresh "B" in let R := fresh "R" in let V := fresh "SV" in
      destruct (rr1s segs m E a k v P) as (b & B & R & V); clear P; rewrite SNV.u_adenot in B
  end.

(* [comment removed for export] *)
Ltac sna_swar4_sx segs m x :=
  lazymatch goal with
  | Hc : Z.land (Z.lor ?A ?B) (18446744071570489472 mod 2 ^ 64) = 0,
    WA : ?A mod 2 ^ 32 = (?S mod 2 ^ 64 + 1179010630) mod 2 ^ 32,
    WB : ?B mod 2 ^ 32 = (?S mod 2 ^ 64 + 18446744072901087184) mod 2 ^ 32 |- _ =>
    lazymatch S with 16777216 * bv_unsigned ?V3 + (256 * ?v1 + (?v0 + 65536 * ?v2)) =>
      lazymatch goal with HV : bv_unsigned V3 mod 256 = ?b3 |- _ =>
        let SW := fresh "SW" in
        pose proof (swar4_bridge_sx v0 v1 v2 b3 (bv_unsigned V3) S A B ltac:(ring) ltac:(sna_lia_t) ltac:(sna_lia_t) ltac:(sna_lia_t)
                      ltac:(sna_lia_t) HV ltac:(sna_lia_t) ltac:(sna_lia_t) WA WB Hc) as SW; SNV.sn_hyps
      end
    end
  end.

(* [comment removed for export] *)
Ltac sna_digs_lit :=
  lazymatch goal with |- SNG.digs ?segs ?m ?x ?k =>
    let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
    let k' := eval vm_compute in k in
    try lazymatch k' with 8 => SNV.sn_swar8 segs m x | 4 => first [ sna_swar4_sx segs m x | SNV.sn_swar4 segs m x ]
                        | 12 => (try SNV.sn_swar8 segs m x); first [ sna_swar4_sx segs m (x + 8) | SNV.sn_swar4 segs m (x + 8) ] end;
    let rec cases n := lazymatch n with
      | 0 => sna_lia_t
      | _ => let n1 := eval vm_compute in (n - 1) in
             destruct (Z.eq_dec j n1) as [->|?]; [ | cases n1 ] end in
    cases k';
    lazymatch goal with |- exists b, SNG.bat _ _ ?xa b /\ _ =>
    match goal with B : SNG.bat _ _ ?y ?b |- _ =>
      assert (y = xa) as _ by ring;
      exists b; split; [apply (SNV.bat_eq segs m y); [exact B | ring] | unfold SNG.isdig; first [split; assumption | sna_lia_t]] end end
  end.

(* [comment removed for export] *)
Ltac sna_with_k N n kont :=
  let rec go ks eqt := lazymatch ks with
    | nil => fail
    | cons ?k ?r => tryif (assert (N = n + k) as _ by eqt) then kont k else go r eqt end in
  let ks := constr:([0; 1; 4; 8; 12; 2; 3; 5; 6; 7; 9; 10; 11]) in
  tryif (go ks ltac:(ring)) then idtac else go ks ltac:(sna_lia_o).

Ltac sna_digs_goal :=
  lazymatch goal with |- SNG.digs ?segs ?m ?a ?N =>
    tryif (lazymatch goal with H : SNG.digs segs m a _ |- _ => idtac end) then
      lazymatch goal with H : SNG.digs segs m a ?n |- _ =>
        sna_with_k N n ltac:(fun k => apply (SNV.digs_app_eq segs m a a n N k eq_refl ltac:(first [ring | sna_lia_t]) ltac:(sna_lia_t) H); sna_digs_lit)
      end
    else sna_with_k N 0 ltac:(fun k => apply (SNV.digs_lit_eq segs m a N k ltac:(first [ring | sna_lia_t])); sna_digs_lit)
  end.

(* [comment removed for export] *)
Ltac sna_nzd_goal0 :=
  lazymatch goal with |- (exists j, 0 <= j < ?il /\ exists b, SNG.bat ?segs ?m (?ip + j) b /\ 49 <= b <= 57) \/
                         (exists j, 0 <= j < 0 /\ exists b, SNG.bat ?segs ?m (?fp + j) b /\ 49 <= b <= 57) =>
    match goal with Ck0 : _ = SNG.cnt0 segs m ?ipz0 (Z.to_nat ?n0) |- _ => pose proof (SNV.cnt0_rng' segs m ipz0 n0 ltac:(lia)) end;
    match goal with
    | Zd : SNG.zdot segs m ?ipz ?n, Ck : ?k = SNG.cnt0 segs m ?ipz (Z.to_nat ?n), D1 : SNG.digs segs m ?ip1 ?il1 |- _ =>
        first [
          match goal with B : SNG.bat segs m ?z ?v |- _ =>
            apply (nzd_intro0 segs m ip il (ipz + n) k fp); [lia | lia
              | apply (SNV.digs_lit_eq segs m ip il il1 ltac:(lia)); replace ip with ip1 by lia; exact D1
              | lia | replace (ipz + n - ip) with n by lia; replace ip with ipz by lia; exact Zd
              | replace (ipz + n - ip) with n by lia; replace ip with ipz by lia; lia
              | left; exists v; split; [apply (SNV.bat_eq segs m z); [exact B | lia] | lia] | lia ] end
        | match goal with B : SNG.bat segs m ?y ?c |- _ =>
            let S1 := fresh "S1" in let S2 := fresh "S2" in
            assert (B' : SNG.bat segs m (ipz + n) c) by (apply (SNV.bat_eq segs m y); [exact B | lia]);
            destruct (SNV.zrun_step segs m ipz n k c ltac:(lia) Zd Ck B' ltac:(lia)) as [S1 S2];
            apply (nzd_intro0 segs m ip il (ipz + (n + 1)) (k + (if Z.eqb c 48 then 1 else 0)) fp); [lia | lia
              | apply (SNV.digs_lit_eq segs m ip il il1 ltac:(lia)); replace ip with ip1 by lia; exact D1
              | lia | replace (ipz + (n + 1) - ip) with (n + 1) by lia; replace ip with ipz by lia; exact S1
              | replace (ipz + (n + 1) - ip) with (n + 1) by lia; replace ip with ipz by lia; symmetry; exact S2
              | right; lia | destruct (Z.eqb_spec c 48); lia ] end ]
    end
  end.

Ltac sna_leaf :=
  lazymatch goal with
  | |- SNG.digs _ _ _ _ => sna_digs_goal
  | |- (exists j, _) \/ (exists j, 0 <= j < 0 /\ _) => first [ sna_nzd_goal0 | SNV.sn_leaf | (exfalso; sna_lia_t) ]
  | |- _ => first [ SNV.sn_leaf | (exfalso; sna_lia_t) ]
  end.

Ltac sna_solve :=
  SNV.sn_pre; sna_sreads; SNV.sn_goal;
  lazymatch goal with HK : know_ok ?segs ?E ?m _ |- _ => SNV.sn_lin segs E m HK; SNV.sn_aluw; SNV.sn_lin segs E m HK end;
  sna_ext; sna_land; sna_bats; SNV.sn_hyps; SNV.sn_clear; sna_hmods; sna_gmods;
  repeat split; solve [sna_leaf].

(* [comment removed for export] *)
Ltac sna_auto :=
  lazymatch goal with
  | |- context [SCReadBase _ 1 true _] => sna_solve
  | |- _ => SNV.sn_solve
  end.

End SNVA.
