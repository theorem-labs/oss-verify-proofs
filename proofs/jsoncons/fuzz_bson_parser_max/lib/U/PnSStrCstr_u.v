(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3 AxSymExec3Sound AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmModel PmModelFacts PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSrcSMemmove_u PnSStrCstrP_u
     Bs0_code_37180_37184_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSSC.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Definition lit (w : bool) : Z := if w then 0x131ef else 0x11f67.
Definition len (w : bool) : Z := if w then 8 else 3.
Definition lbytes (w : bool) : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 (lit w)) (Z.to_nat (len w)) with Some bs => bs | None => [] end.
Lemma lbytes_ok w : rdn RSEGS (fun _ => None) (Z_to_bv 64 (lit w)) (Z.to_nat (len w)) = Some (lbytes w) /\ length (lbytes w) = Z.to_nat (len w).
Proof. destruct w; (split; [vm_compute; reflexivity| vm_compute; reflexivity]). Qed.

(* [comment removed for export] *)
Definition sso (M : word -> option byte) (o n : Z) : Prop := L5.u8_at RSEGS M o (2 * n) /\ L5.defined M (o + 1) n.

Theorem str_cstr_lit (w : bool) fx R M (S o r : Z) :
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 (lit w) -> getr R (reg 1) = Z_to_bv 64 r -> getr R (reg 2) = Z_to_bv 64 S ->
  L5.ra_ok r -> 140735332483120 <= S <= 140737488355328 -> S mod 16 = 0 -> L5.writable RSEGS M (S - 48) 48 ->
  754672 <= o <= 140737488355304 -> L5.writable RSEGS M o 24 -> (S - 48 + 48 <= o \/ o + 24 <= S - 48) -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', msteps RSEGS (st fx R 0x37f44 M) (st fx' R' r M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 48 <= a < S) -> ~ (o <= a < o + 24) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ sso M' o (len w) /\ getr R' (reg 2) = Z_to_bv 64 S
    /\ (forall k, In k [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k)).
Proof.
  intros A10 A11 A1 A2 RA FS F16 WRF Fo WRO DJ IC.
  pose proof RA as (Hr1 & Hr2).
  pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as U8. pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as U9.
  pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as U18. pose proof (bv_unsigned_in_range _ (getr R (reg 19))) as U19.
  pose proof (bv_unsigned_in_range _ (getr R (reg 20))) as U20. unfold bv_modulus in U8, U9, U18, U19, U20.
  set (VV := fun i : nat => match i with 2%nat => S | 33%nat => o | 34%nat => r | 35%nat => len w
        | 36%nat => bv_unsigned (getr R (reg 8)) | 37%nat => bv_unsigned (getr R (reg 9)) | 38%nat => bv_unsigned (getr R (reg 18))
        | 39%nat => bv_unsigned (getr R (reg 19)) | 40%nat => bv_unsigned (getr R (reg 20)) | _ => 0 end).
  (* [comment removed for export] *)
  assert (P1 : exists fx1 R1 M1, mem_grows M M1
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 48 <= i < S - 48 + 48) -> ~ (o + 0 <= i < o + 0 + 1) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ msteps RSEGS (st fx R 0x37f44 M) (st fx1 R1 0xab884 M1)
    /\ getr R1 (reg 1) = Z_to_bv 64 0x37fdc /\ getr R1 (reg 2) = Z_to_bv 64 (S - 48) /\ getr R1 (reg 8) = Z_to_bv 64 (len w)
    /\ getr R1 (reg 10) = Z_to_bv 64 (o + 1) /\ getr R1 (reg 11) = Z_to_bv 64 (lit w) /\ getr R1 (reg 12) = Z_to_bv 64 (len w)
    /\ getr R1 (reg 18) = Z_to_bv 64 o /\ getr R1 (reg 19) = Z_to_bv 64 (o + 1)
    /\ (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k))
    /\ L5.u8_at RSEGS M1 o (2 * len w)
    /\ L5.u64_at RSEGS M1 (S - 48) (bv_unsigned (getr R (reg 20))) /\ L5.u64_at RSEGS M1 (S - 40) (bv_unsigned (getr R (reg 19)))
    /\ L5.u64_at RSEGS M1 (S - 32) (bv_unsigned (getr R (reg 18))) /\ L5.u64_at RSEGS M1 (S - 24) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M1 (S - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M1 (S - 8) r).
  { destruct w; cbn [lit len] in *.
    - (let T := type of (PNSSCP.scCI_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSSCP.scCI_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
      destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & B1 & B2 & B8 & B9 & B10 & B12 & B18 & B19 & C0 & C1 & C2 & C3 & C4 & C5 & C6).
      exists fx1, R1, M1. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|].
      split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B10|]. split; [rewrite (KS1 _) by PMK.inl; exact A11|]. split; [exact B12|].
      split; [exact B18|]. split; [exact B19|]. split; [intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
    - (let T := type of (PNSSCP.scCN_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSSCP.scCN_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
      destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & B1 & B2 & B8 & B9 & B10 & B12 & B18 & B19 & C0 & C1 & C2 & C3 & C4 & C5 & C6).
      exists fx1, R1, M1. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|].
      split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B10|]. split; [rewrite (KS1 _) by PMK.inl; exact A11|]. split; [exact B12|].
      split; [exact B18|]. split; [exact B19|]. split; [intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6]. }
  destruct P1 as (fx1 & R1 & M1 & MG1 & FZ1 & MS1 & B1 & B2 & B8 & B10 & B11 & B12 & B18 & B19 & KS1 & C0 & C1 & C2 & C3 & C4 & C5 & C6).
  pose proof (lbytes_ok w) as (RDL & LENL).
  assert (Hlen : 1 <= len w <= 8) by (destruct w; cbn; clear; lia).
  assert (Hlit : 65536 <= lit w /\ lit w + 8 <= 754672) by (destruct w; cbn; clear; lia).
  (* [comment removed for export] *)
  assert (IC1 : L5.img_clear M1 65536 754672) by (intros i Hi; rewrite FZ1; [apply IC; exact Hi| clear -Hi; lia| clear -Hi FS; lia| clear -Hi Fo; lia]).
  assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (lit w)) (length (lbytes w)) = Some (lbytes w)).
  { rewrite LENL. rewrite (PMCG.rdn_img RSEGS M1 65536 754672 (lit w) (Z.to_nat (len w)) IC1); [exact RDL| clear -Hlit; lia| clear -Hlit; lia| rewrite Z2Nat.id by (clear -Hlen; lia); clear -Hlit Hlen; lia| clear; lia]. }
  assert (WRO1 : L5.writable RSEGS M1 (o + 1) (len w)).
  { apply (L5.writable_sub RSEGS M1 o 24 (o + 1) (len w)); [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WRO)| clear; lia| clear -Hlen; lia]. }
  destruct (PMCPS.memmove_disjoint fx1 M1 (Z_to_bv 64 (o + 1)) (Z_to_bv 64 (lit w)) (len w) (lbytes w) R1 (Z_to_bv 64 0x37fdc)
              ltac:(clear -Hlen; lia) LENL RD1
              ltac:(rewrite LENL; replace (Z_to_bv 64 (o + 1)) with (Z_to_bv 64 (o + 1 + 0)) by (f_equal; clear; lia); apply WRO1; clear -Hlen; lia)
              ltac:(rewrite !L5.unsigned_lit by (clear -Fo Hlit; lia); clear -Fo Hlit Hlen; lia)
              ltac:(rewrite L5.unsigned_lit by (clear -Hlit; lia); clear -Hlit Hlen; lia) ltac:(rewrite L5.unsigned_lit by (clear -Fo; lia); clear -Fo Hlen; lia)
              (L5K.ret_ok_lit 0x37fdc ltac:(split; [clear; lia| reflexivity])) B1 B10 B11 B12) as (R2 & MS2 & KO2 & D10).
  set (M2 := wbytes M1 (Z_to_bv 64 (o + 1)) (lbytes w)) in MS2.
  assert (MG2 : mem_grows M1 M2) by (apply wbytes_grows).
  assert (FZ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (o + 1 <= a < o + 1 + len w) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N. unfold M2. apply PMCP.wbytes_out; [clear -Fo; lia| rewrite LENL; clear -Fo Hlen; lia| exact Ha| rewrite LENL, Z2Nat.id by (clear -Hlen; lia); exact N]. }
  assert (DEF2 : L5.defined M2 (o + 1) (len w)).
  { pose proof (PMCP.wbytes_defined M1 (o + 1) (lbytes w) ltac:(clear -Fo; lia) ltac:(rewrite LENL; clear -Fo Hlen; lia)) as X. rewrite LENL, Z2Nat.id in X by (clear -Hlen; lia). exact X. }
  assert (KS2 : forall i, In i L5K.CS -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; apply (L5K.kept_ok_index R1 R2 i KO2 Hi)).
  assert (AG12 : forall a n, (a + n <= o + 1 \/ o + 1 + len w <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M1 M2 a n).
  { intros a n H Ha Hn i Hi. apply FZ2; [clear -Hi Ha Hn; lia| clear -Hi H; lia]. }
  (* [comment removed for export] *)
  (let T := type of (PNSSCP.scCT_conc fx1 R2 M2 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSSCP.scCT_conc fx1 R2 M2 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS2 _) by PMK.inl; PMK.sc
                         | apply (L5.writable_grows RSEGS M1 M2 _ _ MG2); first [exact (L5.writable_grows RSEGS M M1 _ _ MG1 WRF) | exact (L5.writable_grows RSEGS M M1 _ _ MG1 WRO)]
                         | apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG12; clear -DJ Hlen FS Fo; lia| clear -FS; lia| clear -FS; lia| assumption] ])).
  destruct P as (fx3 & R3 & M3 & MG3 & FW3 & FZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & NUL).
  exists fx3, R3, M3.
  split.
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|].
    apply (PMK.ret_to RSEGS fx3 R3 M3 0x38008 W_37224 r F_37224 eq_refl D_37224 E1 Hr1 Hr2). }
  split; [exact (mem_grows_trans _ _ _ MG1 (mem_grows_trans _ _ _ MG2 MG3))|].
  split.
  { intros a Ha N1 N2. rewrite (FZ3 a Ha) by (clear -N2 Hlen; intros X; apply N2; lia). rewrite (FZ2 a Ha) by (clear -N2 Hlen; intros X; apply N2; lia).
    apply FZ1; [exact Ha| clear -N1; intros X; apply N1; lia| clear -N2; intros X; apply N2; lia]. }
  split.
  { split; [| exact (L5.defined_grows M2 M3 _ _ MG3 DEF2)].
    apply (L5C.u8_at_agree RSEGS M2 M3); [intros i Hi; apply FZ3; clear -Hi Fo; lia| clear -Fo; lia| clear -Fo; lia|].
    apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; apply FZ2; clear -Hi Fo; lia| clear -Fo; lia| clear -Fo; lia| exact C0]. }
  split; [exact E2|].
  intros k Hk.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
    first [ rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned | rewrite E18; apply Z_to_bv_bv_unsigned
          | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
          | rewrite (KS3 _) by PMK.inl; rewrite (KS2 _) by PMK.inl; apply KS1; PMK.inl ].
Qed.

End PNSSC.
