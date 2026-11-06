(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record icells (m : word -> option byte) : Prop := ICells {
  ic_real   : cellN SEGS_B m 0x12c250 8 0x11dfc8;     (* [comment removed for export] *)
  ic_tix0   : cellN SEGS_B m 0x12b150 8 1;            (* [comment removed for export] *)
  ic_tix1   : cellN SEGS_B m 0x12b158 8 18446744073709549568;  (* [comment removed for export] *)
  ic_flagsp : cellN SEGS_B m 0x12a370 8 0x1c4268;     (* [comment removed for export] *)
  ic_verbp  : cellN SEGS_B m 0x12a3d0 8 0x1c21d8;     (* [comment removed for export] *)
  ic_verb   : cellN SEGS_B m 0x1c21d8 4 0;
  ic_dtoff  : cellN SEGS_B m 0x12b160 8 0x8;         (* [comment removed for export] *)
  ic_tsdk   : cellN SEGS_B m 0x131fa4 4 0;            (* [comment removed for export] *)
  ic_inited : cellN SEGS_B m 0x133418 1 1;            (* [comment removed for export] *)
  ic_dtv    : cellN SEGS_B m 0x6667e0 8 0x666808;     (* [comment removed for export] *)
  ic_dtv1   : cellN SEGS_B m 0x666810 8 0x666fe8;     (* [comment removed for export] *)
  ic_treg   : cellN SEGS_B m 0x131fa0 1 1;            (* [comment removed for export] *)
  ic_tsd    : cellN SEGS_B m 0x666790 8 0x687ca0;     (* [comment removed for export] *)
  ic_itls   : cellN SEGS_B m 0x1c42f1 1 1             (* [comment removed for export] *)
}.

Lemma icells_intro : forall m, rt_ok_B m -> ro_ok SEGS_B RO_B m -> icells m.
Proof.
  intros m Hrt Hro. constructor.
  all: first [ apply (cellN_ro_B m); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]
             | apply (cellN_rt_B m); [exact Hrt|vm_compute; reflexivity|lia|cbn; lia] ].
Qed.

Lemma icells_unch : forall m m' lo hi, unch m m' [(lo, hi)] -> 0x688000 <= lo -> icells m -> icells m'.
Proof.
  intros m m' lo hi Hu Hlo H. destruct H. constructor.
  all: eapply cellN_unch; [exact Hu| lia | cbn; lia | intros r [<-|[]]; cbn; lia | assumption].
Qed.

(* [comment removed for export] *)
Record ccells (m : word -> option byte) (CTXp THR t30 t38 DT : Z) : Prop := CCells {
  cc_ctx  : cellN SEGS_B m 0x687ca0 8 CTXp;
  cc_thr  : cellN SEGS_B m (CTXp + 0x98) 8 THR;
  cc_t30  : cellN SEGS_B m (THR + 48) 8 t30;
  cc_t38  : cellN SEGS_B m (THR + 56) 8 t38;
  cc_dt   : cellN SEGS_B m 0x6667f0 8 DT;
  cc_dt18 : cellN SEGS_B m (DT + 24) 8 0x6667e8
}.

(* [comment removed for export] *)
Record mcells (m : word -> option byte) : Prop := MCells {
  mc_1 : cellN SEGS_B m 0x12a380 8 0x132738;  mc_2 : cellN SEGS_B m 0x132738 8 0x7fff8000;
  mc_3 : cellN SEGS_B m 0x12a388 8 0x133428;  mc_4 : cellN SEGS_B m 0x12a390 8 0x133430;
  mc_5 : cellN SEGS_B m 0x133428 8 0;         mc_6 : cellN SEGS_B m 0x133430 8 0;
  mc_7 : cellN SEGS_B m 0x12a398 8 0x133420;  mc_8 : cellN SEGS_B m 0x133420 8 0x7fffffffffff }.

Lemma mcells_intro : forall m, rt_ok_B m -> ro_ok SEGS_B RO_B m -> mcells m.
Proof.
  intros m Hrt Hro. constructor.
  all: first [ apply (cellN_ro_B m); [exact Hro|vm_compute; reflexivity|vm_compute; reflexivity|lia|cbn; lia]
             | apply (cellN_rt_B m); [exact Hrt|vm_compute; reflexivity|lia|cbn; lia] ].
Qed.

Lemma mcells_unch : forall m m' lo hi, unch m m' [(lo, hi)] -> 0x688000 <= lo -> mcells m -> mcells m'.
Proof.
  intros m m' lo hi Hu Hlo H. destruct H. constructor.
  all: eapply cellN_unch; [exact Hu| lia | cbn; lia | intros r [<-|[]]; cbn; lia | assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint probe (fl : Z -> Z) (N h : Z) (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => i
  | S f => if fl ((h + i) mod N) =? 0 then i else probe fl N h f (i + 1)
  end.

Lemma probe_spec : forall fl N h fuel i,
  (exists j, i <= j < i + Z.of_nat fuel /\ fl ((h + j) mod N) = 0) ->
  let r := probe fl N h fuel i in
  i <= r < i + Z.of_nat fuel /\ fl ((h + r) mod N) = 0 /\ forall j, i <= j < r -> fl ((h + j) mod N) <> 0.
Proof.
  intros fl N h fuel. induction fuel as [|f IH]; intros i Hex; cbn [probe].
  - destruct Hex as (j & Hj & _). cbn in Hj. lia.
  - destruct (Z.eqb_spec (fl ((h + i) mod N)) 0) as [H0|H0].
    + split; [lia|]. split; [exact H0|]. intros j Hj. lia.
    + destruct (IH (i + 1)) as (A & B & C).
      { destruct Hex as (j & Hj & Hfl). exists j. split; [|exact Hfl].
        destruct (Z.eq_dec j i) as [->|]; [congruence|lia]. }
      split; [lia|]. split; [exact B|]. intros j Hj.
      destruct (Z.eq_dec j i) as [->|]; [exact H0|]. apply C. lia.
Qed.

(* [comment removed for export] *)
Lemma probe_found : forall fl N h, 0 < N -> 0 <= h ->
  (exists q, 0 <= q < N /\ fl q = 0) ->
  let r := probe fl N h (Z.to_nat N) 0 in
  0 <= r < N /\ fl ((h + r) mod N) = 0 /\ forall j, 0 <= j < r -> fl ((h + j) mod N) <> 0.
Proof.
  intros fl N h HN Hh (q & Hq & Hfl).
  pose proof (probe_spec fl N h (Z.to_nat N) 0) as P. rewrite Z2Nat.id in P by lia. apply P.
  exists ((q - h) mod N). split; [lia|].
  replace ((h + (q - h) mod N) mod N) with q; [exact Hfl|].
  rewrite Zplus_mod_idemp_r. replace (h + (q - h)) with q by lia. symmetry. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation ic_pins := [(2%bv : reg, ZV 32); (4%bv : reg, ZL 0x6667e8); (10%bv : reg, ZL 0x12b150)].
Abbreviation ic_uvi := [Some (0x10007fff8000 + 224, 0x800000000000); Some (1, 0x800000000000 - 160); Some (1, 0x800000000000 - 64);
                        Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (1, 0x800000000000 - 32)].
Abbreviation ic_kn :=
  [KC (ZL 0) 0x12c250 8 (ZL 0x11dfc8); KC (ZL 0) 0x12b150 8 (ZL 1); KC (ZL 0) 0x12b158 8 (ZL 18446744073709549568);
   KC (ZL 0) 0x12a370 8 (ZL 0x1c4268); KC (ZL 0) 0x12a3d0 8 (ZL 0x1c21d8); KC (ZL 0) 0x1c21d8 4 (ZL 0);
   KC (ZL 0) 0x12b160 8 (ZL 0x8); KC (ZL 0) 0x131fa4 4 (ZL 0);
   KC (ZL 0) 0x133418 1 (ZL 1); KC (ZL 0) 0x6667e0 8 (ZL 0x666808); KC (ZL 0) 0x666810 8 (ZL 0x666fe8);
   KC (ZL 0) 0x131fa0 1 (ZL 1); KC (ZL 0) 0x666790 8 (ZL 0x687ca0); KC (ZL 0) 0x1c42f1 1 (ZL 1);
   KC (ZL 0) 0x687ca0 8 (ZV 33); KC (ZV 33) 0x98 8 (ZV 34); KC (ZV 34) 48 8 (ZV 35); KC (ZV 34) 56 8 (ZV 36);
   KC (ZL 0) 0x6667f0 8 (ZV 37); KC (ZV 37) 24 8 (ZL 0x6667e8)].
Abbreviation ic_kw := [KW (ZV 32) (-224) 0].
Abbreviation ic_ctx := (CTX (vi_regs ++ ic_uvi) ic_kn ic_kw).

(* [comment removed for export] *)
Definition IC_KEEP : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Theorem icall : forall regs m (sp CTXp THR t30 t38 DT : Z) (ret : word),
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 4%bv = Z_to_bv 64 TP_B -> getr regs 10%bv = Z_to_bv 64 0x12b150 ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0x10007fff8000 + 224 <= sp -> sp <= 0x800000000000 ->
  mem_def m (sp - 224) 224 ->
  icells m -> ccells m CTXp THR t30 t38 DT ->
  1 <= CTXp -> CTXp + 160 <= 0x800000000000 -> 1 <= THR -> THR + 64 <= 0x800000000000 -> 1 <= DT -> DT + 32 <= 0x800000000000 ->
  (CTXp + 160 <= sp - 224 \/ sp <= CTXp + 152) ->
  (THR + 64 <= sp - 224 \/ sp <= THR + 48) ->
  (DT + 32 <= sp - 224 \/ sp <= DT + 24) ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x60af4) m rom) (mkst regs' ret m' rom)
    /\ getr regs' 10%bv = Z_to_bv 64 FSTLS_B
    /\ keeps IC_KEEP regs regs'
    /\ unch m m' [(sp - 224, sp)] /\ mem_grows m m'.
Proof.
  intros regs m sp CTXp THR t30 t38 DT ret R2 R4 R10 R1 Hret Hsplo Hsphi Hdef IC CC
         Hc1 Hc2 Ht1 Ht2 Hd1 Hd2 Dc Dt Dd.
  unfold TP_B, FSTLS_B in *.
  destruct IC as [I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14]. destruct CC as [C1 C2 C3 C4 C5 C6].
  pose proof (cellN_range _ _ _ _ _ C3) as Rt30. pose proof (cellN_range _ _ _ _ _ C4) as Rt38.
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616 in Rt30, Rt38.
  hide Dc; hide Dt; hide Dd.
  zx_run SEGS_B constr:(ic_ctx) 300%nat (@nil Z) (SCR [] []) constr:(ic_pins) [sp; CTXp; THR; t30; t38; DT] constr:(ic_uvi) regs m rom 0x60af4.
  zx_use2 ZXB
    ltac:(zx_pins)
    ltac:(zx_lia)
    ltac:(kc1 I1; kc1 I2; kc1 I3; kc1 I4; kc1 I5; kc1 I6; kc1 I7; kc1 I8; kc1 I9; kc1 I10; kc1 I11; kc1 I12; kc1 I13; kc1 I14;
          kc1 C1; kc1 C2; kc1 C3; kc1 C4; kc1 C5; kc1 C6; exact I)
    ltac:(kwd Hdef; exact I)
    ltac:(unhide; zx_scs ltac:(lia)).
  unhide. clear ZF.
  assert (R1' : getr regs0 1%bv = ret) by (rewrite <- R1; eapply reg_kept; [exact ZR|reflexivity]).
  eexists regs0, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
  clear ZM.
  split; [zx_regv ZR|].
  split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
  clear ZE ZR.
  split; [unchx | growsx].
Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LOOP_KEEP : list Z := [1; 2; 3; 4; 6; 7; 8; 9; 11; 13; 14; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* [comment removed for export] *)
Abbreviation lp_pins N1 := [(13%bv : reg, ZV 32); (12%bv : reg, ZV 33); (10%bv : reg, ZV 34); (14%bv : reg, ZL N1)].
Abbreviation lp_ctx N LOGN cmin FLAG :=
  (CTX (vi_regs ++ [Some (0x688000, 0x800000000000 - N); Some (0, 18446744073709551615); Some (cmin, N)])
       [KC (ZAdd (ZV 32) (ZModP (ZV 33) LOGN)) 0 1 (ZL FLAG)] []).
(* [comment removed for export] *)
Definition M_KEEP : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Ltac keeps_incl K := eapply keeps_sub_dec; [exact K | vm_compute; reflexivity].

(* [comment removed for export] *)
Ltac pin_kept K ZRprev :=
  lazymatch goal with |- getr _ ?r = _ =>
    let rz := eval vm_compute in (bv_unsigned r) in
    etransitivity; [exact (K rz ltac:(in_list)) | zx_regv ZRprev] end.

(* [comment removed for export] *)
Lemma zero_bytes : forall j, 0 <= j < 8 -> (bv_unsigned (Z_to_bv 64 0) / 2 ^ (8 * j)) mod 256 = 0 mod 256.
Proof.
  intros j Hj. rewrite u_Z2bv64.
  assert (X : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct X as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma fill_step0 : forall M base (K n : Z) a (w : word),
  n = 8 * K + 8 -> a = base + 8 * K -> 0 <= K -> 0 <= base -> base + n <= 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> (bv_unsigned w / 2 ^ (8 * j)) mod 256 = 0 mod 256) ->
  (forall t, 0 <= t < 8 * K -> mem_byte M (base + t) 0) ->
  forall t, 0 <= t < n -> mem_byte (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 w)) (base + t) 0.
Proof.
  intros M base K n a w -> -> HK Hb Hhi Hw HM t Ht.
  destruct (Z.lt_ge_cases t (8 * K)) as [Hlt|Hge].
  - apply mem_byte_wb_out; try (change (Z.of_nat 8) with 8); try lia. apply HM. lia.
  - apply mem_byte_wb_in; try (change (Z.of_nat 8) with 8); try lia. apply Hw. lia.
Qed.

Ltac fill0_go :=
  lazymatch goal with
  | |- forall t, 0 <= t < ?n -> mem_byte _ _ _ =>
      first
        [ let k := eval vm_compute in (n / 8 - 1) in
          let k8 := eval vm_compute in (8 * k) in
          eapply (fill_step0 _ _ k); [reflexivity | lia | lia | lia | lia | exact zero_bytes |];
          change (8 * k) with k8; fill0_go
        | intros ? ?; exfalso; lia ]
  end.

(* [comment removed for export] *)
Ltac mu64_go :=
  lazymatch goal with
  | |- mem_u64 (wbytes _ (Z_to_bv 64 ?a) (word_to_le_bytes 8 _)) ?x _ =>
      first [ replace x with a by ring; apply mem_u64_wb_same; [lia | lia | rewrite ?u_Z2bv64; zwidth; lia]
            | apply mem_u64_wb_out; [lia | zwidth; lia | lia | lia | zwidth; lia | mu64_go] ]
  | |- mem_u64 (wbytes _ (Z_to_bv 64 ?a) _) ?x _ =>
      apply mem_u64_wb_out; [lia | zwidth; lia | lia | lia | zwidth; lia | mu64_go]
  | |- mem_u64 _ _ _ => idtac
  end.
Ltac mbyte_go :=
  lazymatch goal with
  | |- mem_byte (wbytes _ (Z_to_bv 64 ?a) (word_to_le_bytes ?n _)) ?x _ =>
      first [ replace x with a by ring;
              apply mem_byte_wb_in; [lia | zwidth; lia | zwidth; lia | rewrite ?u_Z2bv64, ?Z.sub_diag; vm_compute; reflexivity]
            | apply mem_byte_wb_out; [lia | zwidth; lia | lia | zwidth; lia | mbyte_go] ]
  | |- mem_byte _ _ _ => idtac
  end.

(* [comment removed for export] *)
Abbreviation p0_ctx := (CTX (vi_regs ++ [Some (0x10007fff8000 + 256, 0x800000000000)]) [] [KW (ZV 32) (-256) 0]).
(* [comment removed for export] *)
Abbreviation p2_ctx HOFF := (CTX (vi_regs ++ [Some (0x688000, 0x800000000000 - 11571200); Some (0, 18446744073709551615)])
  [KC (ZL 0) 0x6667e8 8 (ZV 32); KC (ZV 32) 96 1 (ZL 0); KC (ZV 32) 88 8 (ZL 20); KC (ZV 32) HOFF 8 (ZV 33)] []).
(* [comment removed for export] *)
Abbreviation f_pins FLO := [(2%bv : reg, ZAdd (ZV 32) (ZL (-32))); (8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (18%bv : reg, ZL 20);
  (11%bv : reg, ZAdd (ZV 33) (ZL 4096)); (13%bv : reg, ZAdd (ZV 33) (ZL FLO)); (12%bv : reg, ZV 34); (17%bv : reg, ZV 35);
  (15%bv : reg, ZAdd (ZAdd (ZV 33) (ZL FLO)) (ZV 35))].
(* [comment removed for export] *)
Abbreviation f_uvi_hi N := [Some (0x10007fff8000 + 256, 0x800000000000); Some (0x10007fff8000, 0x800000000000 - 11571200);
  Some (0, 18446744073709551615 + 8192); Some (0, N - 1);
  Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (0, 18446744073709551615)].
Abbreviation f_uvi_lo N := [Some (0x10007fff8000 + 256, 0x800000000000); Some (0x688000, 0x7fff7000 - 11571200);
  Some (0, 18446744073709551615 + 8192); Some (0, N - 1);
  Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (0, 18446744073709551615); Some (0, 18446744073709551615)].
Abbreviation f_kn := [KC (ZV 32) (-8) 8 (ZV 36); KC (ZV 32) (-16) 8 (ZV 39); KC (ZV 32) (-24) 8 (ZV 37); KC (ZV 32) (-32) 8 (ZV 38);
   KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL 0x7fff8000);
   KC (ZL 0) 0x12a388 8 (ZL 0x133428); KC (ZL 0) 0x12a390 8 (ZL 0x133430);
   KC (ZL 0) 0x133428 8 (ZL 0); KC (ZL 0) 0x133430 8 (ZL 0);
   KC (ZL 0) 0x12a398 8 (ZL 0x133420); KC (ZL 0) 0x133420 8 (ZL 0x7fffffffffff)].
Abbreviation f_frame FSZ KOFF := (ZAdd (ZAdd (ZV 33) (ZL 36864)) (ZAdd (ZMul (ZV 35) (ZL FSZ)) (ZL KOFF))).
Abbreviation f_ctx UVI FLO FSZ KOFF SHN := (CTX (vi_regs ++ UVI) f_kn
  [KW (ZV 33) 0 11571200; KW (ZAdd (ZAdd (ZV 33) (ZL FLO)) (ZV 35)) 0 1; KW (f_frame FSZ KOFF) 0 FSZ;
   KW (ZDivP (f_frame FSZ KOFF) 3) 2147450880 (2147450880 + SHN)]).

(* [comment removed for export] *)
Ltac cellN_go :=
  lazymatch goal with
  | |- cellN _ (wbytes _ (Z_to_bv 64 ?a) (word_to_le_bytes ?n _)) ?x _ _ =>
      first [ replace x with a by ring; apply cellN_store_same';
              [cbn; lia | lia | zwidth; lia | rewrite ?u_Z2bv64; zwidth; rewrite ?Z.mod_mod by lia; first [reflexivity | apply Z.mod_small; lia | lia] ]
            | apply cellN_store_skip; [lia | zwidth; lia | lia | zwidth; lia | zwidth; lia | cellN_go] ]
  | |- cellN _ _ _ _ _ => first [assumption | idtac]
  end.
