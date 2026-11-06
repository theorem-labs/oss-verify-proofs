(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition zb (z : Z) : byte := Z_to_bv 8 z.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cblock : Type := (Z * Z)%type.   (* [comment removed for export] *)

Definition in_cblock (LB : list cblock) (a : Z) : Prop := exists A n, In (A, n) LB /\ A <= a < A + n.
(* [comment removed for export] *)
Definition in_lframe (LF : list fframe) (a : Z) : Prop :=
  exists F k, In (F, k) LF /\ (F <= a < F + fsz k - 8 \/ SH F <= a < SH F + fsz k / 8).

(* [comment removed for export] *)
Definition ART_WSTATIC : list (Z * Z) := [(0xa6bc0, 0xa6bc8); (0xa6c18, 0x5cc8d0)].
Definition ART_STATIC : list (Z * Z) :=
  ART_WSTATIC ++ [(ADATA_LO, 0xa3000); (0xa3c88, 0xa6518); (0xa6540, 0xa6558); (0xa68a0, 0xa6ba0);
                  (0x5dd1f8, 0x5dd200); (0x5dd248, 0x5dd258); (0x5dd258, 0x5dd260); (0x5dd260, 0x5dd264);
                  (0x5dd278, 0x5dd280); (0x5fd510, 0x5fd518); (0x5fe5f8, 0x5fe600)].
Definition in_zranges (L : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) L /\ lo <= a < hi.
(* [comment removed for export] *)
Definition aclient_image (a : Z) : Prop :=
  (AGERROR0 <= a < AGERROR0 + 8) \/ (AGERROR1 <= a < AGERROR1 + 8)
  \/ (ADATA_LO <= a < AIMG_HI /\ ~ in_zranges ART_WSTATIC a /\ ~ (AERRNO <= a < AERRNO + 4)).

(* [comment removed for export] *)
Definition astack_shadow (sp0 a : Z) : Prop := SH alloc_ceiling <= a < SH (2^47).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cj_client_addr (sp0 : Z) (LB : list cblock) (LF : list fframe) (SP : Z) (a : Z) : Prop :=
  (SP <= a < Z.max (sp0 + 4096) (2^47)) \/ aclient_image a \/ in_cblock LB a \/ in_lframe LF a \/ astack_shadow sp0 a.

Definition cj_pres (sp0 : Z) (LB : list cblock) (LF : list fframe) (SP : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> cj_client_addr sp0 LB LF SP a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

(* [comment removed for export] *)
Definition cj_write_ok (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (iv : Z * Z) : Prop :=
  snd iv <= fst iv
  \/ (alloc_ceiling <= fst iv /\ snd iv <= SPB)                                   (* [comment removed for export] *)
  \/ (SH alloc_ceiling <= fst iv /\ snd iv <= SH SPB)                           (* [comment removed for export] *)
  \/ (AERRNO <= fst iv /\ snd iv <= AERRNO + 4)
  \/ (AGERROR0 <= fst iv /\ snd iv <= AGERROR0 + 8) \/ (AGERROR1 <= fst iv /\ snd iv <= AGERROR1 + 8)
  \/ (ADATA_LO <= fst iv /\ snd iv <= AIMG_HI /\ forall a, fst iv <= a < snd iv -> ~ in_zranges ART_STATIC a)  (* [comment removed for export] *)
  \/ (exists A n, In (A, n) LB /\ A <= fst iv /\ snd iv <= A + n)                 (* [comment removed for export] *)
  \/ (exists F k, In (F, k) LF /\ F <= fst iv /\ snd iv <= F + fsz k - 8)         (* [comment removed for export] *)
  \/ (exists F k, In (F, k) LF /\ SH F <= fst iv /\ snd iv <= SH F + fsz k / 8).  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ablock_range (A n : Z) : Prop :=
  AIMG_HI <= A /\ A mod 16 = 0 /\ 0 <= n /\ A + Z.max n 1 <= alloc_ceiling.

Fixpoint cb_remove (A : Z) (LB : list cblock) : list cblock :=
  match LB with
  | [] => []
  | (B, n) :: LB' => if Z.eqb B A then LB' else (B, n) :: cb_remove A LB'
  end.

(* [comment removed for export] *)
Definition ACJST (m : word -> option byte) : Prop :=
  cells_at asegs m AHOOKS [C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)]
  /\ (exists e0 : word, rw_cells asegs m AGERROR0 [C8 e0])
  /\ (exists e1 : word, rw_cells asegs m AGERROR1 [C8 e1])
  /\ cells_at asegs m ALCONV [C8 (wz ADOTSTR)].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shb (m : word -> option byte) (a v : Z) : Prop := m (wa (SH a)) = Some (zb v).

(* [comment removed for export] *)
Definition shadow_ok (m : word -> option byte) (a n : Z) : Prop :=
  (forall i, 0 <= i < n ->
      exists v, shb m (a + i) v /\ (v = 0 \/ ((a + i) mod 8 < v /\ v < 8)))
  /\ (forall j, (SH a) / 8 * 8 <= j < (SH (a + n - 1)) / 8 * 8 + 8 -> m (wa j) <> None).

(* [comment removed for export] *)
Definition shcells (vs : list Z) : list cell := map (fun v => C1 (zb v)) vs.

(* [comment removed for export] *)
Definition ARTCELLS (m : word -> option byte) : Prop :=
  (cells_at asegs m 0xa1f80 [C8 (Z_to_bv 64 0xaa278)] /\ cells_at asegs m 0xaa278 [C8 (Z_to_bv 64 0x7fff8000)])   (* [comment removed for export] *)
  /\ (cells_at asegs m 0xa1fd8 [C8 (Z_to_bv 64 0xaa280)] /\ cells_at asegs m 0xaa280 [C4 (Z_to_bv 64 1)])         (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1f88 [C8 (Z_to_bv 64 0xaaf68)] /\ cells_at asegs m 0xaaf68 [C8 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1f90 [C8 (Z_to_bv 64 0xaaf70)] /\ cells_at asegs m 0xaaf70 [C8 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1f98 [C8 (Z_to_bv 64 0xaaf60)] /\ cells_at asegs m 0xaaf60 [C8 (Z_to_bv 64 0x7fffffffffff)] (* [comment removed for export] *)
  /\ cells_at asegs m 0xa2ae8 [C8 (Z_to_bv 64 0xaaf59)]                                                             (* [comment removed for export] *)
  /\ cells_at asegs m 0xaaf58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                                                    (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1f70 [C8 (Z_to_bv 64 0x13bda8)]                                                             (* [comment removed for export] *)
  /\ cells_at asegs m (0x13bda8 + 245) [C1 (Z_to_bv 8 0)] /\ cells_at asegs m (0x13bda8 + 251) [C1 (Z_to_bv 8 1)]        (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3e00 [C8 (Z_to_bv 64 A_MUSL_MEMCPY)] /\ cells_at asegs m 0xa3e08 [C8 (Z_to_bv 64 A_MUSL_MEMSET)]  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3c88 [C8 (Z_to_bv 64 A_MUSL_STRLEN)] /\ cells_at asegs m 0xa3cb0 [C8 (Z_to_bv 64 0x9b0f4)]       (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa9adc [C1 (Z_to_bv 8 1)]                                                  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1fa0 [C8 (Z_to_bv 64 0xa3e08)]                                          (* [comment removed for export] *)
  /\ cells_at asegs m 0x13be20 [C8 (Z_to_bv 64 0xffffffffffffffff)]                               (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1f60 [C8 (Z_to_bv 64 0x139d20)] /\ cells_at asegs m 0x139d20 [C8 (Z_to_bv 64 4096)]  (* [comment removed for export] *)
  /\ cells_at asegs m 0x13be38 [C8 (Z_to_bv 64 0)]                                                 (* [comment removed for export] *)
  /\ cells_at asegs m 0x13be9c [C1 (Z_to_bv 8 1)] /\ cells_at asegs m 0x13be83 [C1 (Z_to_bv 8 1)]    (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1fc0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x13bd9c)]                       (* [comment removed for export] *)
  /\ cells_at asegs m 0x13bd9c [C4 (Z_to_bv 64 0)]                                                 (* [comment removed for export] *)
  /\ cells_at asegs m 0x5fd510 [C8 (Z_to_bv 64 4096)]                                               (* [comment removed for export] *)
  /\ cells_at asegs m 0xa2c08 [C8 (Z_to_bv 64 0x5fd290)] /\ (exists canary : word, cells_at asegs m 0x5fd290 [C8 canary])  (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cells_at asegs m 0x13bdfc [C1 (Z_to_bv 8 1)]                                                  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3d08 [C8 (Z_to_bv 64 0x9ab0c)] /\ cells_at asegs m 0xa3d00 [C8 (Z_to_bv 64 0x9a964)]  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3cf8 [C8 (Z_to_bv 64 0x94664)] /\ cells_at asegs m 0xa3ce0 [C8 (Z_to_bv 64 0x9ab20)]  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3ce8 [C8 (Z_to_bv 64 0x9709c)] /\ cells_at asegs m 0xa3cf0 [C8 (Z_to_bv 64 0x9a948)]  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3cb8 [C8 (Z_to_bv 64 0x906c4)]                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa1f78 [C8 (Z_to_bv 64 0xa7a78)]                                          (* [comment removed for export] *)
  /\ cells_at asegs m 0xa7a90 [C4 (Z_to_bv 64 1)]                                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7b30 [C8 (Z_to_bv 64 0)]                                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6bc0 [C8 (Z_to_bv 64 1)]                                                 (* [comment removed for export] *)
  /\ cells_at asegs m 0xa2bf8 [C8 (Z_to_bv 64 0xa68a0)] /\ cells_at asegs m 0xa2c00 [C8 (Z_to_bv 64 0xa6ba0)]  (* [comment removed for export] *)
  /\ (forall a, 0xa68a0 <= a < 0xa6ba0 -> m (wa a) = None)                                        (* [comment removed for export] *)
  /\ cells_at asegs m 0x13c120 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3cc0 [C8 (Z_to_bv 64 0xa0954)]                                          (* [comment removed for export] *)
  /\ cells_at asegs m 0xa3db0 [C8 (Z_to_bv 64 0x9badc)].                                         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive uwt (m : word -> option byte) (lo top pc0 : Z) : Z -> Z -> Z -> list Z -> Prop :=
| uwt_stop : forall prev f k,
    (f <= prev \/ f mod 8 <> 0 \/ top - 16 <= f \/ TRACE_MAX_LEN <= k) ->
    uwt m lo top pc0 prev f k []
| uwt_lowpc : forall prev f k (nxt pc1 : word),
    prev < f -> f mod 8 = 0 -> f < top - 16 -> k < TRACE_MAX_LEN -> lo + 16 <= f ->
    bytes_at asegs m (f - 16) (le8 nxt ++ le8 pc1) -> bv_unsigned pc1 < 4096 ->
    uwt m lo top pc0 prev f k []
| uwt_hop : forall prev f k (nxt pc1 : word) tl,
    prev < f -> f mod 8 = 0 -> f < top - 16 -> k < TRACE_MAX_LEN -> lo + 16 <= f ->
    bytes_at asegs m (f - 16) (le8 nxt ++ le8 pc1) -> 4096 <= bv_unsigned pc1 ->
    uwt m lo top pc0 f (bv_unsigned nxt) (k + (if bv_unsigned pc1 =? pc0 then 0 else 1)) tl ->
    uwt m lo top pc0 prev f k ((if bv_unsigned pc1 =? pc0 then [] else [bv_unsigned pc1]) ++ tl).

(* [comment removed for export] *)
Definition hop1_ok (sp0 sp : Z) : bool := (ASTACK_BOTTOM sp0 <? sp) && (sp + 16 <? ASTACK_TOP sp0) && (sp mod 8 =? 0).
Definition hook_tr (pc0 sp0 sp ra : Z) (tl : list Z) : list Z := if hop1_ok sp0 sp then pc0 :: ra :: tl else [pc0].
Lemma hook_tr_ok : forall pc0 sp0 sp ra tl, hop1_ok sp0 sp = true -> hook_tr pc0 sp0 sp ra tl = pc0 :: ra :: tl.
Proof. intros. unfold hook_tr. rewrite H. reflexivity. Qed.
Lemma hook_tr_ko : forall pc0 sp0 sp ra tl, hop1_ok sp0 sp = false -> hook_tr pc0 sp0 sp ra tl = [pc0].
Proof. intros. unfold hook_tr. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition trs_put (tr : list Z) (TRS TRS' : list (list Z)) : Prop :=
  (In tr TRS /\ TRS' = TRS) \/ (~ In tr TRS /\ TRS' = tr :: TRS).
(* [comment removed for export] *)
Definition trs_room (tr : list Z) (TRS : list (list Z)) : Prop :=
  In tr TRS \/ Z.of_nat (length TRS) < DEPOT_KMAX.

(* [comment removed for export] *)
Definition gmono (g g' : lghost) : Prop := forall w, In w (g_win g) -> In w (g_win g').

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_pres_refl : forall sp0 LB LF SP m, cj_pres sp0 LB LF SP m m.
Proof. intros sp0 LB LF SP m a _ _. auto. Qed.

Lemma cj_pres_trans : forall sp0 LB LF SP m1 m2 m3,
  cj_pres sp0 LB LF SP m1 m2 -> cj_pres sp0 LB LF SP m2 m3 -> cj_pres sp0 LB LF SP m1 m3.
Proof.
  intros sp0 LB LF SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma cj_pres_weaken : forall sp0 LB LB' LF LF' SP SP' m m',
  cj_pres sp0 LB LF SP m m' -> SP <= SP' ->
  (forall b, In b LB' -> In b LB) -> (forall f, In f LF' -> In f LF) -> cj_pres sp0 LB' LF' SP' m m'.
Proof.
  intros sp0 LB LB' LF LF' SP SP' m m' H HS HL HF a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|Hc]]]];
    [left; lia| right; left; exact Hc| right; right; left| right; right; right; left| do 4 right; exact Hc].
  - exists A, n. split; [apply HL; exact Hb| exact Hr].
  - exists F, k. split; [apply HF; exact Hb| exact Hr].
Qed.

Definition cj_client_range (sp0 : Z) (LB : list cblock) (LF : list fframe) (SP : Z) (A n : Z) : Prop :=
  (SP <= A /\ A + n <= Z.max (sp0 + 4096) (2^47))
  \/ (AGERROR0 <= A /\ A + n <= AGERROR0 + 8) \/ (AGERROR1 <= A /\ A + n <= AGERROR1 + 8)
  \/ (exists B k, In (B, k) LB /\ B <= A /\ A + n <= B + k)
  \/ (exists F k, In (F, k) LF /\ F <= A /\ A + n <= F + fsz k - 8)
  \/ (exists F k, In (F, k) LF /\ SH F <= A /\ A + n <= SH F + fsz k / 8)
  \/ (SH alloc_ceiling <= A /\ A + n <= SH (2^47))
  \/ (ADATA_LO <= A /\ A + n <= AIMG_HI /\ (forall a, A <= a < A + n -> ~ in_zranges ART_WSTATIC a) /\ (A + n <= AERRNO \/ AERRNO + 4 <= A)).

Lemma cj_client_range_addr : forall sp0 LB LF SP A n a,
  cj_client_range sp0 LB LF SP A n -> A <= a < A + n -> cj_client_addr sp0 LB LF SP a.
Proof.
  intros sp0 LB LF SP A n a HR Ha. unfold cj_client_range, cj_client_addr, aclient_image, in_cblock, in_lframe, astack_shadow in *.
  destruct HR as [H|[H|[H|[(B & k & Hb & H1 & H2)|[(F & k & Hb & H1 & H2)|[(F & k & Hb & H1 & H2)|[H|(H1 & H2 & H3 & H4)]]]]]]];
    [left; lia| right; left; lia| right; left; lia
    | right; right; left; exists B, k; split; [exact Hb|lia]
    | right; right; right; left; exists F, k; split; [exact Hb|lia]
    | right; right; right; left; exists F, k; split; [exact Hb|lia]
    | do 4 right; lia
    | right; left; do 2 right; split; [lia| split; [apply H3; lia| lia]]].
Qed.

Lemma cj_pres_bytes_at : forall sp0 LB LF SP m m' A bs,
  cj_pres sp0 LB LF SP m m' -> bytes_at asegs m A bs -> cj_client_range sp0 LB LF SP A (Z.of_nat (length bs)) ->
  bytes_at asegs m' A bs.
Proof.
  intros sp0 LB LF SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply cj_client_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma cj_pres_wr_at : forall sp0 LB LF SP m m' A n,
  cj_pres sp0 LB LF SP m m' -> wr_at asegs m A n -> cj_client_range sp0 LB LF SP A n -> wr_at asegs m' A n.
Proof.
  intros sp0 LB LF SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply cj_client_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma cj_pres_rw_cells : forall sp0 LB LF SP m m' A cs,
  cj_pres sp0 LB LF SP m m' -> rw_cells asegs m A cs -> cj_client_range sp0 LB LF SP A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m' A cs.
Proof.
  intros sp0 LB LF SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply cj_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply cj_pres_wr_at; eauto.
Qed.

Lemma cj_pres_stk : forall sp0 LB LF SP m m' lo hi,
  cj_pres sp0 LB LF SP m m' -> stk asegs m lo hi -> SP <= lo -> hi <= sp0 + 4096 -> stk asegs m' lo hi.
Proof.
  intros sp0 LB LF SP m m' lo hi HP ST HS Hh. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmts.
(* [comment removed for export] *)
Variable ART : Z -> Z -> list cblock -> list fframe -> list (list Z) -> Z ->
               (word -> option byte) -> Model -> lghost -> Prop.

(* [comment removed for export] *)
Definition amalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (tr : list Z)
    (n lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                           (errv' : word) (TRS' : list (list Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv']
    /\ cj_pres sp0 LB LF (bv_unsigned sp) m m'
    /\ gmono g g' /\ (trs_put tr TRS TRS' \/ TRS' = TRS)   (* [comment removed for export] *)
    /\ ( (a0 = wz 0 /\ ART sp0 SPB LB LF TRS' (B - cost_malloc n) m' mo' g')
         \/ (exists (A : Z) (junk : list byte),
               a0 = wz A /\ ablock_range A n /\ ~ In A (map fst LB)
               /\ (forall F k, In (F, k) LF -> A + n <= F \/ F + fsz k <= A)
               /\ ART sp0 SPB ((A, n) :: LB) LF TRS' (B - cost_malloc n) m' mo' g'
               /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
               /\ Forall (fun b => b = zb MALLOC_FILL_BYTE) (firstn (Z.to_nat (Z.min n MALLOC_FILL_MAX)) junk)) ).

Definition malloc_lscps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (n lo : Z) (errv : word) (tl : list Z),
  ART sp0 SPB LB LF TRS B m mo g ->
  bv_unsigned sp <= SPB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP ->
  a0 = wz n -> 0 <= n < 2^32 ->
  cost_malloc n <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_MALLOC ->          (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_MALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) TRS ->
  LSCPS asegs (amalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                            (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) n lo m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AMALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition afree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (tr : list Z)
    (A lo : Z) (errv : word) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                           (TRS' : list (list Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv]                       (* [comment removed for export] *)
    /\ cj_pres sp0 (cb_remove A LB) LF (bv_unsigned sp) m m'
    /\ gmono g g' /\ trs_put tr TRS TRS'
    /\ ART sp0 SPB (cb_remove A LB) LF TRS' (B - cost_free) m' mo' g'.

Definition free_lscps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (A n lo : Z) (errv : word) (tl : list Z),
  ART sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
  bv_unsigned sp <= SPB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP ->
  a0 = wz A ->
  cost_free <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_FREE ->          (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (hook_tr PC0_FREE sp0 (bv_unsigned sp) (bv_unsigned ra) tl) TRS ->
  LSCPS asegs (afree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                          (hook_tr PC0_FREE sp0 (bv_unsigned sp) (bv_unsigned ra) tl) A lo errv m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AFREE) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition afree_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
    (lo : Z) (errv : word) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv]
    /\ cj_pres sp0 LB LF (bv_unsigned sp) m m'
    /\ gmono g g'
    /\ ART sp0 SPB LB LF TRS B m' mo' g'.

Definition free_null_lscps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (lo : Z) (errv : word) (tl : list Z),
  ART sp0 SPB LB LF TRS B m mo g ->
  bv_unsigned sp <= SPB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP ->
  a0 = wz 0 ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_FREE ->          (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_FREE (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  LSCPS asegs (afree_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B lo errv m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AFREE) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition arealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (tr : list Z)
    (A k n lo : Z) (old : list byte) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                           (errv' : word) (TRS' : list (list Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv']
    /\ gmono g g' /\ (trs_put tr TRS TRS' \/ TRS' = TRS)   (* [comment removed for export] *)
    /\ ( (a0 = wz 0 /\ ART sp0 SPB LB LF TRS' (B - cost_realloc n) m' mo' g' /\ cj_pres sp0 LB LF (bv_unsigned sp) m m')
         \/ (exists (Bn : Z) (junk : list byte),
               a0 = wz Bn /\ ablock_range Bn n /\ ~ In Bn (map fst LB)
               /\ (forall F k, In (F, k) LF -> Bn + n <= F \/ F + fsz k <= Bn)
               /\ ART sp0 SPB ((Bn, n) :: cb_remove A LB) LF TRS' (B - cost_realloc n) m' mo' g'
               /\ cj_pres sp0 (cb_remove A LB) LF (bv_unsigned sp) m m'
               /\ rw_cells asegs m' Bn [CB (Z.to_nat (Z.min k n)) (firstn (Z.to_nat (Z.min k n)) old);
                                       CB (Z.to_nat (n - Z.min k n)) junk]) ).

Definition realloc_lscps_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (A k n lo : Z) (old : list byte) (errv : word) (tl : list Z),
  ART sp0 SPB LB LF TRS B m mo g -> In (A, k) LB -> bytes_at asegs m A old -> Z.of_nat (length old) = k ->
  bv_unsigned sp <= SPB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP ->
  a0 = wz A -> a1 = wz n -> 0 < n < 2^32 ->
  cost_realloc n <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_REALLOC ->          (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_REALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) TRS ->
  LSCPS asegs (arealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                             (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) A k n lo old m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AREALLOC) fc None m (seg_rom asegs)) mo g.

Definition realloc_null_lscps_stmt : Prop :=   (* [comment removed for export] *)
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
         (n lo : Z) (errv : word) (tl : list Z),
  ART sp0 SPB LB LF TRS B m mo g ->
  bv_unsigned sp <= SPB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  rw_cells asegs m AERRNO [C4 errv] ->
  mem_inv asegs m ->
  tp = wz ATP ->
  a0 = wz 0 -> a1 = wz n -> 0 <= n < 2^32 ->
  cost_malloc n <= B ->
  4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_REALLOC ->          (* [comment removed for export] *)
  uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_REALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
  trs_room (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) TRS ->
  LSCPS asegs (amalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                            (hook_tr PC0_REALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) n lo m g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz AREALLOC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Definition astkmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
    (k lo : Z) (errv : word) (m : word -> option byte) (mo : Model) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                           (Fr : Z) (junk : list byte) (fl : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AERRNO [C4 errv]                                  (* [comment removed for export] *)
    /\ cj_pres sp0 LB LF (bv_unsigned sp) m m'
    /\ g' = g /\ mo' = mo
    /\ a0 = wz Fr /\ Fr mod fsz k = 0 /\ AIMG_HI <= Fr /\ Fr + fsz k <= alloc_ceiling
    /\ ~ In Fr (map fst LF)
    /\ (forall A n, In (A, n) LB -> A + n <= Fr \/ Fr + fsz k <= A)
    /\ ART sp0 SPB LB ((Fr, k) :: LF) TRS B m' mo' g'
    /\ rw_cells asegs m' Fr [CB (Z.to_nat (fsz k - 8)) junk]
    /\ cells_at asegs m' (Fr + fsz k - 8) [C8 (wz fl)]
    /\ rw_cells asegs m' (SH Fr) (shcells (repeat 0 (Z.to_nat (fsz k / 8)))).

Definition stkmalloc_lscps_stmt (k : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (lo : Z) (errv : word),
  ART sp0 SPB LB LF TRS B m mo g ->
  bv_unsigned sp <= SPB ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ASTKMALLOC_STACK ->
  mem_inv asegs m ->
  tp = wz ATP ->
  rw_cells asegs m AERRNO [C4 errv] ->
  lf_count k LF < fcap k ->                      (* [comment removed for export] *)
  LSCPS asegs (astkmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B k lo errv m mo g)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (wz (if k =? 1 then ASTKMALLOC1 else ASTKMALLOC2)) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint strncmp_spec (x y : list Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => match x, y with
            | a :: x', b :: y' => if a =? b then (if a =? 0 then 0 else strncmp_spec x' y' n') else (if a <? b then (-1) else 1)
            | _, _ => 0   (* [comment removed for export] *)
            end
  end.
Fixpoint strncmp_stop (x y : list Z) (n : nat) : nat :=   (* [comment removed for export] *)
  match n with
  | O => O
  | S n' => match x, y with
            | a :: x', b :: y' => if (a =? b) && negb (a =? 0) then S (strncmp_stop x' y' n') else O
            | _, _ => O
            end
  end.


(* [comment removed for export] *)

End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record art_iface : Type := mkARTI {
  ART : Z -> Z -> list cblock -> list fframe -> list (list Z) -> Z -> (word -> option byte) -> Model -> lghost -> Prop;
  (* [comment removed for export] *)
  art_binv : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g -> LOK asegs mo /\ BINV mo g /\ 0 <= B <= g_res g;
  art_frame : forall sp0 SPB LB LF TRS B m m' mo g W,
      ART sp0 SPB LB LF TRS B m mo g -> munch W m m' -> wmono asegs m m' ->
      Forall (cj_write_ok sp0 SPB LB LF) W -> ART sp0 SPB LB LF TRS B m' mo g;
  art_perm : forall sp0 SPB LB LB' LF LF' TRS B m mo g,
      ART sp0 SPB LB LF TRS B m mo g -> Permutation LB LB' -> Permutation LF LF' -> ART sp0 SPB LB' LF' TRS B m mo g;
  art_lower : forall sp0 SPB SPB' LB LF TRS B B' m mo g,
      ART sp0 SPB LB LF TRS B m mo g -> SPB' <= SPB -> 0 <= B' <= B -> ART sp0 SPB' LB LF TRS B' m mo g;
  art_block_range : forall sp0 SPB LB LF TRS B m mo g A n, ART sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> ablock_range A n;
  art_blocks_disjoint : forall sp0 SPB LB LF TRS B m mo g A1 n1 A2 n2,
      ART sp0 SPB LB LF TRS B m mo g -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 ->
      A1 + Z.max n1 1 + 16 <= A2 \/ A2 + Z.max n2 1 + 16 <= A1;      (* [comment removed for export] *)
  art_nodup : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g -> NoDup (map fst LB) /\ NoDup (map fst LF);
  art_block_wr : forall sp0 SPB LB LF TRS B m mo g A n, ART sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> wr_at asegs m A n;
  (* [comment removed for export] *)
  art_block_slack : forall sp0 SPB LB LF TRS B m mo g A n i, ART sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
      0 <= i -> A + n + i < roundup (A + Z.max n 1) 16 -> m (wa (A + n + i)) <> None;
  (* [comment removed for export] *)
  art_shadow : forall sp0 SPB LB LF TRS B m mo g A n, ART sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
      cells_at asegs m (SH A) (shcells (shadow_enc (Z.max n 1))) /\ shadow_ok m A n;
  (* [comment removed for export] *)
  art_frame_facts : forall sp0 SPB LB LF TRS B m mo g Fr k, ART sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
      (k = 1 \/ k = 2) /\ Fr mod fsz k = 0 /\ AIMG_HI <= Fr /\ Fr + fsz k <= alloc_ceiling
      /\ wr_at asegs m Fr (fsz k - 8) /\ wr_at asegs m (SH Fr) (fsz k / 8)
      /\ (exists fl, cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] /\ rw_cells asegs m fl [C1 (zb 1)]
                     /\ (forall A n, In (A, n) LB -> fl < A - 16 \/ A + n <= fl) /\ fl + 1 <= Fr - 8 )
      /\ (forall A n, In (A, n) LB -> A + n + 16 <= Fr \/ Fr + fsz k <= A - 16);
  (* [comment removed for export] *)
  art_flag_high : forall sp0 SPB LB LF TRS B m mo g Fr k fl, ART sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
      cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] -> 0 <= fl < 2^64 -> ablk fl (fl + 1);
  (* [comment removed for export] *)
  art_frames_disjoint : forall sp0 SPB LB LF TRS B m mo g F1 k1 F2 k2, ART sp0 SPB LB LF TRS B m mo g ->
      In (F1, k1) LF -> In (F2, k2) LF -> F1 <> F2 -> F1 + fsz k1 <= F2 \/ F2 + fsz k2 <= F1;
  (* [comment removed for export] *)
  art_ff_release : forall sp0 SPB LB LF TRS B m m' mo g Fr k fl,
      ART sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
      cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] ->
      munch [(fl, fl + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' fl [C1 (zb 0)] ->
      ART sp0 SPB LB (lf_remove Fr LF) TRS B m' mo g;
  (* [comment removed for export] *)
  art_global_shadow : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g ->
      Forall (fun gs => shadow_ok m (fst gs) (snd gs)) AGLOB_STRS /\ shadow_ok m AHOOKS 24
      /\ shadow_ok m AGERROR0 8 /\ shadow_ok m AGERROR1 8;
  art_cjst : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g -> ACJST m;
  art_ssp : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g ->
      cells_at asegs m AGOT_SSP [C8 (wz ASSP)] /\ exists canary : word, cells_at asegs m ASSP [C8 canary];
  art_rtcells : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g -> ARTCELLS m;
  (* [comment removed for export] *)
  art_lowshadow : forall sp0 SPB LB LF TRS B m mo g, ART sp0 SPB LB LF TRS B m mo g ->
      forall a, SH AIMG_LO <= a < SH AIMG_HI -> rw_cells asegs m a [C1 (zb (alowsh a))];
  (* [comment removed for export] *)
  art_model_frame : forall sp0 SPB LB LF TRS B m mo mo' g, ART sp0 SPB LB LF TRS B m mo g ->
      m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None ->
      ART sp0 SPB LB LF TRS B m mo' g;
  (* [comment removed for export] *)
  art_malloc : malloc_lscps_stmt ART;
  art_free : free_lscps_stmt ART;
  art_free_null : free_null_lscps_stmt ART;
  art_realloc : realloc_lscps_stmt ART;
  art_realloc_null : realloc_null_lscps_stmt ART;
  art_stkmalloc1 : stkmalloc_lscps_stmt ART 1;
  art_stkmalloc2 : stkmalloc_lscps_stmt ART 2;
  (* [comment removed for export] *)
  art_block_band : forall sp0 SPB LB LF TRS B m mo g A n, ART sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
      ablk A (A + Z.max n 1);
  art_frame_band : forall sp0 SPB LB LF TRS B m mo g Fr k, ART sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
      ablk Fr (Fr + fsz k)
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ablock_range_high : forall A n,
  KHIGHMEM_BEG <= A -> A mod 16 = 0 -> 0 <= n -> A + Z.max n 1 <= alloc_ceiling -> ablock_range A n.
Proof. intros A n H1 H2 H3 H4. unfold ablock_range, KHIGHMEM_BEG, AIMG_HI in *. repeat split; try assumption. lia. Qed.

Lemma ablock_range_low : forall A n,
  AIMG_HI <= A -> A mod 16 = 0 -> 0 <= n -> A + Z.max n 1 <= KLOWSHADOW_BEG -> ablock_range A n.
Proof.
  intros A n H1 H2 H3 H4. unfold ablock_range. repeat split; try assumption.
  pose proof alloc_ceiling_range as R. unfold KLOWSHADOW_BEG in H4. lia.
Qed.

Lemma ablk_ablock_range : forall A n, ablk A (A + Z.max n 1) -> A mod 16 = 0 -> 0 <= n -> ablock_range A n.
Proof. intros A n HB H2 H3. pose proof (ablk_lin _ _ HB) as (L1 & _ & L3 & _). unfold ablock_range. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma ablock_range_lin : forall A n, ablock_range A n ->
  A + Z.max n 1 + 8 <= 2^47 /\ KLOWSHADOW_BEG < SH A /\ SH (A + Z.max n 1) < KHIGHMEM_BEG.
Proof.
  intros A n (H1 & _ & Hn & HC). pose proof alloc_ceiling_range as R.
  assert (A1 : AIMG_HI / 8 <= A / 8) by (apply Z.div_le_mono; [lia| exact H1]).
  assert (A2 : (A + Z.max n 1) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  unfold SH, SHADOW_OFFSET, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *.
  change (0x5ff000 / 8) with 0xbfe00 in A1. change (0x7fffff800000 / 8) with 0xffffff00000 in A2. lia.
Qed.

(* [comment removed for export] *)
Lemma art_block_clear_band : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g A n a,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG -> ~ (A <= a < A + Z.max n 1).
Proof. intros AI sp0 SPB LB LF TRS B m mo g A n a HL IN. exact (ablk_clear_band _ _ a (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN)). Qed.
Lemma art_block_shad_disj : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g A n,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> A + Z.max n 1 <= SH A \/ SH (A + Z.max n 1 + 7) + 1 <= A.
Proof. intros AI sp0 SPB LB LF TRS B m mo g A n HL IN. apply (ablk_shad_disj _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL IN)). lia. Qed.

End CeilWrap.
