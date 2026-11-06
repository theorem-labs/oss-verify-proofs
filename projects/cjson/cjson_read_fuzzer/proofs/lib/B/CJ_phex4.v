(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
Module CJ_pbuf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition pbuf_cells (content length offset depth : Z) : list cell :=
  [C8 (wz content); C8 (wz length); C8 (wz offset); C8 (wz depth); C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)].

Definition pbuf_at (m : word -> option byte) (P content length offset depth : Z) : Prop :=
  rw_cells bsegs m P (pbuf_cells content length offset depth).

Lemma pbuf_cells_size : forall c l o d, cells_size (pbuf_cells c l o d) = 56%nat.
Proof. reflexivity. Qed.

Lemma pbuf_at_bound : forall m P c l o d, pbuf_at m P c l o d -> 0 <= P /\ P + 56 <= 2^64.
Proof. intros. pose proof (rw_cells_bound bsegs _ _ _ H) as HB. rewrite pbuf_cells_size in HB. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pbuf_sh (m : word -> option byte) (P : Z) : Prop := sh_zero m P (P + 56).

(* [comment removed for export] *)
Definition text_sh (m : word -> option byte) (CA blen : Z) : Prop :=
  forall a, CA <= a < CA + blen -> shchk m a 1.

Lemma text_sh_of_shadow_ok : forall m A n CA blen,
  shadow_ok m A n -> A <= CA -> CA + blen <= A + n -> text_sh m CA blen.
Proof. intros m A n CA blen SO H1 H2 a Ha. eapply shadow_ok_shchk1; [exact SO| lia]. Qed.

Lemma text_sh_sub : forall m CA blen CA' blen',
  text_sh m CA blen -> CA <= CA' -> CA' + blen' <= CA + blen -> text_sh m CA' blen'.
Proof. intros m CA blen CA' blen' H H1 H2 a Ha. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma text_sh_munch : forall W m m' CA blen,
  text_sh m CA blen -> munch W m m' -> 0 <= CA -> CA + blen <= 2^47 ->
  disjoint_from W (SH CA) (SH (CA + blen - 1) + 1 - SH CA) -> text_sh m' CA blen.
Proof.
  intros W m m' CA blen H MU H0 H1 HD a Ha.
  pose proof (SH_mono CA a ltac:(lia)). pose proof (SH_mono a (CA + blen - 1) ltac:(lia)).
  pose proof (SH_bounds a ltac:(lia)).
  destruct (H a Ha) as (v & Hv & Cv). exists v. split; [|exact Cv].
  eapply shb_munch; [exact Hv| exact MU| lia|].
  eapply disjoint_outside; [exact HD|]. lia.
Qed.

Lemma pbuf_sh_munch : forall W m m' P,
  pbuf_sh m P -> munch W m m' -> 0 <= P -> P + 56 <= 2^47 ->
  disjoint_from W (SH P) (SH (P + 55) + 1 - SH P) -> pbuf_sh m' P.
Proof.
  intros W m m' P H MU H0 H1 HD. unfold pbuf_sh in *.
  pose proof (SH_bounds P ltac:(lia)). pose proof (SH_bounds (P + 56 - 1) ltac:(lia)).
  eapply sh_zero_munch; [exact H| exact MU| lia| lia|].
  replace (P + 56 - 1) with (P + 55) by lia. exact HD.
Qed.

(* [comment removed for export] *)
Lemma pbuf_sh_ext : forall m m' P,
  pbuf_sh m P -> (forall j, SH P <= j <= SH (P + 55) -> m' (wa j) = m (wa j)) -> pbuf_sh m' P.
Proof.
  intros m m' P H E. unfold pbuf_sh in *. eapply sh_zero_ext; [exact H|].
  replace (P + 56 - 1) with (P + 55) by lia. exact E.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ws_count (bs : list byte) : nat :=
  match bs with
  | [] => O
  | b :: bs' => if Z.leb (bv_unsigned b) 32 then S (ws_count bs') else O
  end.

Lemma ws_count_le : forall bs, (ws_count bs <= length bs)%nat.
Proof. induction bs as [|b bs IH]; cbn; [lia|]. destruct (Z.leb _ _); cbn; lia. Qed.

Lemma ws_count_lt : forall bs i, (i < ws_count bs)%nat -> exists b, nth_error bs i = Some b /\ bv_unsigned b <= 32.
Proof.
  induction bs as [|b bs IH]; intros i Hi; cbn in Hi; [lia|].
  destruct (Z.leb_spec (bv_unsigned b) 32); [|lia].
  destruct i as [|i]; [exists b; split; [reflexivity| assumption]|].
  cbn. apply IH. lia.
Qed.

Lemma ws_count_stop : forall bs b, nth_error bs (ws_count bs) = Some b -> 32 < bv_unsigned b.
Proof.
  induction bs as [|b0 bs IH]; intros b Hn; cbn in Hn; [discriminate|].
  destruct (Z.leb_spec (bv_unsigned b0) 32); [apply IH; exact Hn|]. inversion Hn; subst. lia.
Qed.

Lemma ws_count_skipn : forall bs i, (i <= ws_count bs)%nat -> (ws_count (skipn i bs) + i = ws_count bs)%nat.
Proof.
  induction bs as [|b bs IH]; intros i Hi; cbn in Hi |- *.
  - destruct i; cbn; lia.
  - destruct (Z.leb_spec (bv_unsigned b) 32).
    + destruct i as [|i]; cbn. { destruct (Z.leb_spec (bv_unsigned b) 32); lia. } specialize (IH i). lia.
    + assert (i = O) by lia. subst i. cbn. destruct (Z.leb_spec (bv_unsigned b) 32); lia.
Qed.

(* [comment removed for export] *)
Definition skipws_off (bs : list byte) (off : Z) : Z :=
  let len := Z.of_nat (length bs) in
  if (0 <=? off) && (off <? len) then
    let k := off + Z.of_nat (ws_count (skipn (Z.to_nat off) bs)) in
    if k =? len then len - 1 else k
  else off.

Lemma skipws_off_noop : forall bs off, Z.of_nat (length bs) <= off -> skipws_off bs off = off.
Proof.
  intros bs off H. unfold skipws_off. destruct (Z.leb_spec 0 off); [|reflexivity]. cbn [andb].
  destruct (Z.ltb_spec off (Z.of_nat (length bs))); [lia| reflexivity].
Qed.

Lemma skipws_off_range : forall bs off, 0 <= off < Z.of_nat (length bs) ->
  off <= skipws_off bs off < Z.of_nat (length bs).
Proof.
  intros bs off H. unfold skipws_off.
  destruct (Z.leb_spec 0 off); [|lia]. destruct (Z.ltb_spec off (Z.of_nat (length bs))); [|lia]. cbn [andb].
  pose proof (ws_count_le (skipn (Z.to_nat off) bs)) as HL. rewrite length_skipn in HL.
  destruct (Z.eqb_spec (off + Z.of_nat (ws_count (skipn (Z.to_nat off) bs))) (Z.of_nat (length bs))); lia.
Qed.

(* [comment removed for export] *)
Lemma skipws_off_result : forall bs off, 0 <= off < Z.of_nat (length bs) ->
  let off' := skipws_off bs off in
  (forall i, off <= i < off' -> exists b, nth_error bs (Z.to_nat i) = Some b /\ bv_unsigned b <= 32)
  /\ ( (exists b, nth_error bs (Z.to_nat off') = Some b /\ 32 < bv_unsigned b)
       \/ (off' = Z.of_nat (length bs) - 1 /\ forall i, off <= i <= off' -> exists b, nth_error bs (Z.to_nat i) = Some b /\ bv_unsigned b <= 32) ).
Proof.
  intros bs off H. unfold skipws_off.
  destruct (Z.leb_spec 0 off); [|lia]. destruct (Z.ltb_spec off (Z.of_nat (length bs))); [|lia]. cbn [andb].
  set (rest := skipn (Z.to_nat off) bs).
  pose proof (ws_count_le rest) as HL. unfold rest in HL at 2. rewrite length_skipn in HL.
  assert (WS : forall i, off <= i < off + Z.of_nat (ws_count rest) ->
                 exists b, nth_error bs (Z.to_nat i) = Some b /\ bv_unsigned b <= 32).
  { intros i Hi. destruct (ws_count_lt rest (Z.to_nat i - Z.to_nat off)) as (b & Hn & Hb); [lia|].
    exists b. split; [|exact Hb]. unfold rest in Hn. rewrite nth_error_skipn in Hn.
    replace (Z.to_nat off + (Z.to_nat i - Z.to_nat off))%nat with (Z.to_nat i) in Hn by lia. exact Hn. }
  destruct (Z.eqb_spec (off + Z.of_nat (ws_count rest)) (Z.of_nat (length bs))) as [E|NE]; cbn zeta.
  - split. { intros i Hi. apply WS. lia. } right. split; [reflexivity|]. intros i Hi. apply WS. lia.
  - split. { exact WS. } left.
    destruct (nth_error bs (Z.to_nat (off + Z.of_nat (ws_count rest)))) as [b|] eqn:En.
    2:{ apply nth_error_None in En. lia. }
    exists b. split; [reflexivity|]. apply (ws_count_stop rest). unfold rest at 1. rewrite nth_error_skipn.
    rewrite <- En. f_equal. lia.
Qed.


End CeilWrap.
End CJ_pbuf.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_traces.
Module CJ_parse_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_traces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PARSE_HEX4   : Z := 0x863a8.
Definition PARSE_STRING : Z := 0x853ac.
Definition PARSE_VALUE  : Z := 0x82db0.
Definition PARSE_OBJECT : Z := 0x85b38.
Definition PARSE_WLOPTS : Z := 0x8285c.   (* [comment removed for export] *)
Definition PARSE_WOPTS  : Z := 0x827f4.   (* [comment removed for export] *)

Definition DELETE_ENTRY : Z := 0x82614.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PARSE_HEX4_STACK : Z := 16.
Definition PARSE_STRING_STACK : Z := 144 + AMALLOC_STACK.                (* [comment removed for export] *)
Definition DELETE_STACK (d : nat) : Z := 80 * Z.of_nat d + AMALLOC_STACK. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PARSE_STACK (depth : Z) : Z := 384 * (1001 - depth) + 16384.   (* [comment removed for export] *)
Definition POBJ_STACK (depth : Z) : Z := 144 + PARSE_STACK (depth + 1).  (* [comment removed for export] *)
Definition PARSE_DOC_STACK : Z := 176 + PARSE_STACK 0.                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PV_RATE : Z := 640.
Definition PV_FRATE : Z := PV_RATE + cost_free.                             (* [comment removed for export] *)
Definition pv_cost_pre (L : Z) : Z := PV_FRATE * L + 256.
Definition pdoc_cost (L : Z) : Z := 448 + pv_cost_pre L + cost_free.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition Fagree (F F' : bvmap 5 word) : Prop :=
  forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k.

Lemma Fagree_refl : forall F, Fagree F F.
Proof. intros F k _ _ _. reflexivity. Qed.
Lemma Fagree_trans : forall F1 F2 F3, Fagree F1 F2 -> Fagree F2 F3 -> Fagree F1 F3.
Proof. intros F1 F2 F3 H1 H2 k A B C. rewrite (H2 k A B C). apply H1; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hex4_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (b4 : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte) (h : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' A b4
    /\ 0 <= h < 2^16.

Definition hex4_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A lo : Z) (b4 : list byte),
  bytes_at bsegs m A b4 -> length b4 = 4%nat -> A + 4 <= alloc_ceiling ->
  shbase_cells m -> text_sh m A 4 ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PARSE_HEX4_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 A ->
  evt bsegs (hex4_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A b4 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PARSE_HEX4) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pv_addr (sp0 : Z) (LR : list cblock) (LF : list fframe) (SP P : Z) (a : Z) : Prop :=
  cj_client_addr sp0 LR LF SP a /\ ~ (AERRNO <= a < AERRNO + 4) /\ ~ (P <= a < P + 56).
Definition ppres (sp0 : Z) (LR : list cblock) (LF : list fframe) (SP P : Z) (m m' : word -> option byte) : Prop :=
  magree (pv_addr sp0 LR LF SP P) m m'.

(* [comment removed for export] *)
Definition doc_addr (sp0 : Z) (LB : list cblock) (LF : list fframe) (SP : Z) (a : Z) : Prop :=
  cj_client_addr sp0 LB LF SP a /\ ~ (AERRNO <= a < AERRNO + 4)
  /\ ~ (AGERROR0 <= a < AGERROR0 + 8) /\ ~ (AGERROR1 <= a < AGERROR1 + 8).
Definition dpres (sp0 : Z) (LB : list cblock) (LF : list fframe) (SP : Z) (m m' : word -> option byte) : Prop :=
  magree (doc_addr sp0 LB LF SP) m m'.

Lemma ppres_refl : forall sp0 LR LF SP P m, ppres sp0 LR LF SP P m m.
Proof. intros; apply magree_refl. Qed.
Lemma ppres_trans : forall sp0 LR LF SP P m1 m2 m3,
  ppres sp0 LR LF SP P m1 m2 -> ppres sp0 LR LF SP P m2 m3 -> ppres sp0 LR LF SP P m1 m3.
Proof. intros; eapply magree_trans; eauto. Qed.
Lemma dpres_refl : forall sp0 LB LF SP m, dpres sp0 LB LF SP m m.
Proof. intros; apply magree_refl. Qed.
Lemma dpres_trans : forall sp0 LB LF SP m1 m2 m3,
  dpres sp0 LB LF SP m1 m2 -> dpres sp0 LB LF SP m2 m3 -> dpres sp0 LB LF SP m1 m3.
Proof. intros; eapply magree_trans; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition parse_inv (AI : art_iface) (TI : trs_iface) (m : word -> option byte) (mo : Model) (g : lghost)
    (sp0 SPB : Z) (LB X LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B : Z)
    (U P CA blen : Z) (bs : list byte) (D n lo SP : Z) (errv : word) : Prop :=
  ART AI sp0 SPB LB LF TRS B m mo g
  /\ Permutation ((U, 64) :: X ++ LR) LB
  /\ In (D, n) LR /\ D <= CA /\ CA + blen <= D + n
  /\ bytes_at bsegs m CA bs /\ Z.of_nat (length bs) = blen /\ blen < 2^31
  /\ rw_cells bsegs m AERRNO [C4 errv]
  /\ mem_inv bsegs m
  /\ stk bsegs m lo SP /\ alloc_ceiling <= lo
  /\ TINV TI np TRS
  /\ In (P - 32, 1) LF /\ pbuf_sh m P
  /\ 0 <= SP /\ SP <= SPB /\ SPB < 2^62 /\ SP + 16 < ASTACK_TOP sp0 /\ sp0 <= 2^47
  /\ ASTACK_BOTTOM sp0 <= lo /\ SP mod 16 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pstr_fail_cost (L : Z) : Z := 281 * L + 192 + cost_free.
(* [comment removed for export] *)
Definition pstr_cost_pre (L : Z) : Z := pstr_fail_cost L.

Section S.
  Variable AI : art_iface.
  Variable TI : trs_iface.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition PSTR_TR_MALLOC : list Z := [PC0_MALLOC; 0x85558].
  Definition PSTR_TR_FREE : list Z := [PC0_FREE; 0x85a04].

  Definition parse_string_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np B : Z) (U P CA blen off depth : Z) (bs : list byte)
      (D n lo : Z) (m : word -> option byte) (g : lghost)
      (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z)
      : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                          (r : Z) (off' : Z) (LB' X : list cblock) (TRS' : list (list Z)) (B' : Z) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ a0 = wz r
      /\ parse_inv AI TI m' mo' g' sp0 SPB LB' X LR LF TRS' np B' U P CA blen bs D n lo (bv_unsigned sp) errv'
      /\ ppres sp0 LR LF (bv_unsigned sp) P m m'
      /\ gmono g g'
      /\ pbuf_at m' P CA blen off' depth /\ off <= off' <= blen
      /\ ( (r = 0 /\ X = [] /\ rw_cells bsegs m' U (node_cells nx pv ch ty p1 vs vi p2 vd ky)
             /\ B - pstr_fail_cost (blen - off) <= B')
           \/ (r = 1 /\ exists (S k : Z), X = [(S, k)] /\ S <> 0
                 /\ rw_cells bsegs m' U (node_cells nx pv ch 16 p1 S vi p2 vd ky)
                 /\ cj_str m' S [(S, k)]
                 /\ 1 <= k <= off' - off /\ B' = B - cost_malloc k) ).

  Definition parse_string_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B : Z)
           (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (errv : word)
           (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z),
      parse_inv AI TI m mo g sp0 SPB LB [] LR LF TRS np B U P CA blen bs D n lo (bv_unsigned sp) errv ->
      rw_cells bsegs m U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
      pbuf_at m P CA blen off depth -> 0 <= off < blen ->
      lo <= bv_unsigned sp - PARSE_STRING_STACK ->
      tp = wz ATP -> a0 = wz U -> a1 = wz P ->
      STAT TI PSTR_TR_MALLOC -> STAT TI PSTR_TR_FREE ->
      pstr_cost_pre (blen - off) <= B ->
      LSCPS bsegs (parse_string_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B U P CA blen off depth bs D n lo m g
                     nx pv ch ty p1 vs vi p2 vd ky)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_STRING) fc None m (seg_rom bsegs)) mo g.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition delete_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np B0 : Z) (nb : nat) (lo : Z) (errv : word)
      (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                          (LR' : list cblock) (TRS' : list (list Z)),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' AERRNO [C4 errv]
      /\ ART AI sp0 SPB LR' LF TRS' (B0 - cost_free * Z.of_nat nb) m' mo' g' /\ Permutation LR' LR
      /\ TINV TI np TRS' /\ gmono g g'
      /\ cj_pres sp0 LR LF (bv_unsigned sp) m m'.

  Definition delete_spec_at (d : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (T : Z -> Prop) (sp0 SPB : Z) (LB LR B : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B0 : Z)
           (p lo : Z) (errv : word),
      ART AI sp0 SPB LB LF TRS B0 m mo g ->
      cj_chain T m d p B ->
      Permutation (B ++ LR) LB ->
      bv_unsigned sp <= SPB -> sp0 <= 2^47 -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> bv_unsigned sp mod 16 = 0 ->
      stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> ASTACK_BOTTOM sp0 <= lo -> lo <= bv_unsigned sp - DELETE_STACK d ->
      rw_cells bsegs m AERRNO [C4 errv] ->
      mem_inv bsegs m ->
      tp = wz ATP ->
      a0 = wz p ->
      TINV TI np TRS -> Forall (STAT TI) S_DELETE ->
      cost_free * Z.of_nat (length B) <= B0 ->
      LSCPS bsegs (delete_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B0 (length B) lo errv m g)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DELETE_ENTRY) fc None m (seg_rom bsegs)) mo g.

  Definition cjson_delete_stmt : Prop := forall d, delete_spec_at d.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pv_trace (ra : Z) (CH : list (Z * Z * Z)) (b : nat) : list Z :=
    trunc30 (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 b ++ ra :: map fr_ra CH).

  Definition parse_value_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z))
      (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (m : word -> option byte) (g : lghost)
      (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z)
      : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (r : Z) (off' depth' : Z) (LB' X : list cblock) (TRS' : list (list Z)) (B' : Z) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ a0 = wz r
      /\ Fagree F F' /\ frm0 fc'
      /\ parse_inv AI TI m' mo' g' sp0 SPB LB' X LR LF TRS' np B' U P CA blen bs D n lo (bv_unsigned sp) errv'
      /\ ppres sp0 LR LF (bv_unsigned sp) P m m'
      /\ gmono g g' /\ chain_cells m' CH
      /\ pbuf_at m' P CA blen off' depth'
      /\ ( (r = 0 /\ X = [] /\ rw_cells bsegs m' U (node_cells nx pv 0 ty p1 0 vi p2 vd ky)
             /\ B - pv_cost_pre (blen - off) <= B')
           \/ (r = 1 /\ depth' = depth /\ off <= off' <= blen /\ B - PV_RATE * (off' - off) <= B'
               /\ Z.of_nat (length X) <= off' - off
               /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                    X = Bv ++ Bc
                    /\ rw_cells bsegs m' U (node_cells nx pv ch ty' p1 vs vi' p2 vd' ky)
                    /\ CJ_PRINTABLE ty'
                    /\ cj_str m' vs Bv
                    /\ cj_chain CJ_PRINTABLE m' dc ch Bc
                    /\ Z.of_nat dc + depth <= 1000) ).

  (* [comment removed for export] *)
  Definition parse_value_at (nfuel : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B : Z) (CH : list (Z * Z * Z))
           (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (errv : word)
           (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z),
      parse_inv AI TI m mo g sp0 SPB LB [] LR LF TRS np B U P CA blen bs D n lo (bv_unsigned sp) errv ->
      rw_cells bsegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      pbuf_at m P CA blen off depth -> 0 <= off <= blen -> 0 <= depth <= 1000 ->
      blen - off <= Z.of_nat nfuel ->
      lo <= bv_unsigned sp - PARSE_STACK depth -> bv_unsigned sp mod 16 = 0 ->
      frm0 fc -> tp = wz ATP -> a0 = wz U -> a1 = wz P ->
      lf_room 2 LF (1001 - depth) ->
      chain_cells m CH -> chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0) -> chain_link (bv_unsigned s0) (bv_unsigned sp) CH ->
      4096 <= bv_unsigned ra -> ~ is_pc0 (bv_unsigned ra) ->
      (forall b, STAT TI (pv_trace (bv_unsigned ra) CH b)) -> (forall b, STAT TI (tr_pv_pobj b)) ->
      Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE) ->
      pv_cost_pre (blen - off) <= B ->
      LSCPS bsegs (parse_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                    nx pv ty p1 vi p2 vd ky)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_VALUE) fc None m (seg_rom bsegs)) mo g.

  Definition parse_value_stmt : Prop := forall nfuel, parse_value_at nfuel.

  (* [comment removed for export] *)
  Definition parse_object_at (nfuel : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B : Z)
           (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (errv : word)
           (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z),
      parse_inv AI TI m mo g sp0 SPB LB [] LR LF TRS np B U P CA blen bs D n lo (bv_unsigned sp) errv ->
      rw_cells bsegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      pbuf_at m P CA blen off depth -> 0 <= off <= blen -> 0 <= depth <= 1000 ->
      blen - off <= Z.of_nat nfuel ->
      lo <= bv_unsigned sp - POBJ_STACK depth -> bv_unsigned sp mod 16 = 0 ->
      frm0 fc -> tp = wz ATP -> a0 = wz U -> a1 = wz P ->
      lf_room 2 LF (1000 - depth) ->
      (forall b, STAT TI (tr_pv_pobj b)) -> Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE) ->
      pv_cost_pre (blen - off) <= B ->
      LSCPS bsegs (parse_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B [] U P CA blen off depth bs D n lo m g
                    nx pv ty p1 vi p2 vd ky)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_OBJECT) fc None m (seg_rom bsegs)) mo g.

  Definition parse_object_stmt : Prop := forall nfuel, parse_object_at nfuel.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition parse_doc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (sp0 SPB : Z) (LB : list cblock) (np B : Z) (CA blen : Z) (bs : list byte) (lo : Z)
      (m : word -> option byte) (g : lghost)
      : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (r : Z) (LB' : list cblock) (TRS' : list (list Z)) (B' : Z) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ a0 = wz r
      /\ Fagree F F' /\ frm0 fc'
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' AERRNO [C4 errv']
      /\ ART AI sp0 SPB LB' [] TRS' B' m' mo' g' /\ TINV TI np TRS' /\ gmono g g'
      /\ B - pdoc_cost blen <= B'
      /\ bytes_at bsegs m' CA bs
      /\ dpres sp0 LB [] (bv_unsigned sp) m m'
      /\ ( (r = 0 /\ Permutation LB' LB)
           \/ (r <> 0 /\ exists (B2 : list cblock) (d : nat) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word),
                 cj_chain CJ_PRINTABLE m' d r B2 /\ (d <= 1001)%nat
                 /\ Permutation LB' (B2 ++ LB)
                 /\ Z.of_nat (length B2) <= blen + 1                          (* [comment removed for export] *)
                 /\ rw_cells bsegs m' r (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0)) ).

  (* [comment removed for export] *)
  Definition parse_doc_pre (sp s0 ra tp : word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
      (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (np B : Z) (D n lo blen : Z) (errv : word) : Prop :=
    ART AI sp0 SPB LB [] TRS B m mo g /\ TINV TI np TRS /\ In (D, n) LB
    /\ rw_cells bsegs m AERRNO [C4 errv] /\ mem_inv bsegs m
    /\ stk bsegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ ASTACK_BOTTOM sp0 <= lo /\ lo <= bv_unsigned sp - PARSE_DOC_STACK
    /\ 0 <= bv_unsigned sp /\ bv_unsigned sp <= SPB /\ SPB < 2^62 /\ bv_unsigned sp + 16 < ASTACK_TOP sp0 /\ sp0 <= 2^47
    /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned s0 <= bv_unsigned sp /\ 4096 <= bv_unsigned ra /\ ~ is_pc0 (bv_unsigned ra)
    /\ frm0 fc /\ tp = wz ATP
    /\ STAT TI [PC0_MALLOC; 0x829e8; bv_unsigned ra]
    /\ (forall site b, In site PWLO_PV_RAS -> STAT TI (tr_pv_pwlo_at site (bv_unsigned ra) b)) /\ (forall b, STAT TI (tr_pv_pobj b))
    /\ Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE)
    /\ pdoc_cost blen <= B.

  Definition parse_wlopts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (np B : Z)
           (CA blen : Z) (bs : list byte) (D n lo : Z) (errv : word),
      parse_doc_pre sp s0 ra tp fc m mo g sp0 SPB LB TRS np B D n lo blen errv ->
      D <= CA -> CA + blen <= D + n ->
      bytes_at bsegs m CA bs -> Z.of_nat (length bs) = blen -> blen < 2^31 ->
      a0 = wz CA -> a1 = wz blen -> a2 = wz 0 ->
      LSCPS bsegs (parse_doc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB np B CA blen bs lo m g)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_WLOPTS) fc None m (seg_rom bsegs)) mo g.

  (* [comment removed for export] *)
  Definition parse_wopts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (np B : Z)
           (V : Z) (str : list byte) (D n lo : Z) (errv : word),
      parse_doc_pre sp s0 ra tp fc m mo g sp0 SPB LB TRS np B D n lo (Z.of_nat (length str) + 1) errv ->
      D <= V -> V + Z.of_nat (length str) + 1 <= D + n ->
      bytes_at bsegs m V (str ++ [wb 0]) -> ~ In (wb 0) str -> Z.of_nat (length str) + 1 < 2^31 ->
      a0 = wz V -> a1 = wz 0 ->
      LSCPS bsegs (parse_doc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB np B V (Z.of_nat (length str) + 1) (str ++ [wb 0]) lo m g)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_WOPTS) fc None m (seg_rom bsegs)) mo g.
End S.


End CeilWrap.
End CJ_parse_iface.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_parse_lemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv CJ_parse_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia. Qed.

Lemma nth_error_lt_some : forall {X} (l : list X) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof.
  intros X l i H. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Definition at_ (bs : list byte) (i : Z) : Z :=
  match nth_error bs (Z.to_nat i) with Some b => bv_unsigned b | None => 0 end.

Lemma at__nth : forall bs i b, 0 <= i -> nth_error bs (Z.to_nat i) = Some b -> at_ bs i = bv_unsigned b.
Proof. intros bs i b _ H. unfold at_. rewrite H. reflexivity. Qed.

Lemma at__range : forall bs i, 0 <= at_ bs i < 256.
Proof. intros bs i. unfold at_. destruct (nth_error bs (Z.to_nat i)); [apply byte_range| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Scan.
  Variable bs : list byte.
  Variable blen : Z.
  Notation AT := (at_ bs).

  (* [comment removed for export] *)
  Fixpoint ps_scan (fuel : nat) (e skipped : Z) : option (Z * Z) :=
    match fuel with
    | O => None
    | S f =>
        if e <? blen then
          if AT e =? 34 then Some (e, skipped)
          else if AT e =? 92 then
                 if blen <=? e + 1 then None else ps_scan f (e + 2) (skipped + 1)
               else ps_scan f (e + 1) skipped
        else None
    end.

  (* [comment removed for export] *)
  Fixpoint npairs (fuel : nat) (q i : Z) : Z :=
    match fuel with
    | O => 0
    | S f =>
        if q <? i then
          if (q <? blen) && negb (AT q =? 34) then
            if AT q =? 92 then 1 + npairs f (q + 2) i else npairs f (q + 1) i
          else 0
        else 0
    end.

  Lemma npairs_nonneg : forall fuel q i, 0 <= npairs fuel q i.
  Proof.
    induction fuel as [|f IH]; intros q i; cbn [npairs]; [lia|].
    destruct (q <? i); [|lia]. destruct (_ && _); [|lia]. destruct (AT q =? 92); pose proof (IH (q + 2) i); pose proof (IH (q + 1) i); lia.
  Qed.

  Lemma npairs_le : forall fuel q i, i <= q -> npairs fuel q i = 0.
  Proof. intros [|f] q i H; cbn [npairs]; [reflexivity|]. destruct (Z.ltb_spec q i); [lia| reflexivity]. Qed.

  Definition bflag (i : Z) : Z := if AT i =? 92 then 1 else 0.
  Lemma bflag_range : forall i, 0 <= bflag i <= 1.
  Proof. intros i. unfold bflag. destruct (AT i =? 92); lia. Qed.

  (* [comment removed for export] *)
  Lemma npairs_window : forall fuel q i j, i <= j ->
    0 <= npairs fuel q j - npairs fuel q i /\ 2 * (npairs fuel q j - npairs fuel q i) <= j - i + bflag i.
  Proof.
    induction fuel as [|f IH]; intros q i j Hij.
    - cbn. pose proof (bflag_range i). lia.
    - pose proof (bflag_range i) as Bi.
      destruct (Z_lt_le_dec q j) as [Qj|Qj].
      2:{ rewrite !(npairs_le (S f)) by lia. lia. }
      destruct (Z_lt_le_dec q i) as [Qi|Qi].
      + cbn [npairs]. replace (q <? j) with true by (symmetry; apply Z.ltb_lt; lia). replace (q <? i) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct ((q <? blen) && negb (AT q =? 34)); [|lia].
        destruct (AT q =? 92); [specialize (IH (q + 2) i j Hij)| specialize (IH (q + 1) i j Hij)]; lia.
      + rewrite (npairs_le (S f) q i) by lia. rewrite Z.sub_0_r.
        cbn [npairs]. replace (q <? j) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct ((q <? blen) && negb (AT q =? 34)); [|lia].
        destruct (Z.eqb_spec (AT q) 92) as [E|NE].
        * pose proof (npairs_nonneg f (q + 2) j) as N0.
          assert (Bq : i = q -> bflag i = 1) by (intros ->; unfold bflag; rewrite E; reflexivity).
          destruct (Z_le_gt_dec (q + 2) j) as [L|L].
          -- destruct (IH (q + 2) (q + 2) j L) as [_ W]. rewrite (npairs_le f (q + 2) (q + 2)) in W by lia.
             pose proof (bflag_range (q + 2)). destruct (Z.eq_dec i q) as [->|NEQ]; [specialize (Bq eq_refl)|]; lia.
          -- rewrite (npairs_le f (q + 2) j) by lia. destruct (Z.eq_dec i q) as [->|NEQ]; [specialize (Bq eq_refl)|]; lia.
        * pose proof (npairs_nonneg f (q + 1) j) as N0.
          destruct (Z_le_gt_dec (q + 1) j) as [L|L].
          -- destruct (IH (q + 1) (q + 1) j L) as [_ W]. rewrite (npairs_le f (q + 1) (q + 1)) in W by lia.
             pose proof (bflag_range (q + 1)). lia.
          -- rewrite (npairs_le f (q + 1) j) by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ps_scan_npairs : forall fuel q sk e sk',
    ps_scan fuel q sk = Some (e, sk') -> sk' = sk + npairs fuel q e /\ q <= e < blen /\ AT e = 34.
  Proof.
    induction fuel as [|f IH]; intros q sk e sk' H; cbn [ps_scan npairs] in *; [discriminate|].
    destruct (Z.ltb_spec q blen) as [LT|]; [|discriminate]. cbn [andb] in *.
    destruct (Z.eqb_spec (AT q) 34) as [E34|N34].
    - inversion H; subst. rewrite Z.ltb_irrefl. cbn. lia.
    - cbn [negb]. destruct (AT q =? 92).
      + destruct (blen <=? q + 1); [discriminate|]. destruct (IH _ _ _ _ H) as (Hs & Hq & Ha).
        replace (q <? e) with true by (symmetry; apply Z.ltb_lt; lia). lia.
      + destruct (IH _ _ _ _ H) as (Hs & Hq & Ha). replace (q <? e) with true by (symmetry; apply Z.ltb_lt; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ps_scan_npairs_end : forall fuel q sk e sk' i,
    ps_scan fuel q sk = Some (e, sk') -> e <= i -> npairs fuel q i = npairs fuel q e.
  Proof.
    induction fuel as [|f IH]; intros q sk e sk' i H Hi; cbn [ps_scan npairs] in *; [reflexivity|].
    destruct (Z.ltb_spec q blen) as [LT|]; [|discriminate]. cbn [andb] in *.
    destruct (Z.eqb_spec (AT q) 34) as [E34|N34].
    - inversion H; subst. rewrite Z.ltb_irrefl. cbn. destruct (e <? i); reflexivity.
    - cbn [negb]. destruct (AT q =? 92).
      + destruct (blen <=? q + 1); [discriminate|]. pose proof (ps_scan_npairs _ _ _ _ _ H) as (_ & Hq & _).
        replace (q <? i) with true by (symmetry; apply Z.ltb_lt; lia). replace (q <? e) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite (IH _ _ _ _ _ H Hi). reflexivity.
      + pose proof (ps_scan_npairs _ _ _ _ _ H) as (_ & Hq & _).
        replace (q <? i) with true by (symmetry; apply Z.ltb_lt; lia). replace (q <? e) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite (IH _ _ _ _ _ H Hi). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ps_scan_step : forall f q sk, q < blen ->
    ps_scan (S f) q sk =
      if AT q =? 34 then Some (q, sk)
      else if AT q =? 92 then (if blen <=? q + 1 then None else ps_scan f (q + 2) (sk + 1))
      else ps_scan f (q + 1) sk.
  Proof. intros f q sk Hq. cbn [ps_scan]. replace (q <? blen) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ps_scan_fuel : forall f q sk r, ps_scan f q sk = Some r -> forall f', (f <= f')%nat -> ps_scan f' q sk = Some r.
  Proof.
    induction f as [|f IH]; intros q sk r H f' Hf; cbn [ps_scan] in H; [discriminate|].
    destruct f' as [|f']; [lia|]. cbn [ps_scan].
    destruct (q <? blen); [|discriminate]. destruct (AT q =? 34); [exact H|].
    destruct (AT q =? 92).
    - destruct (blen <=? q + 1); [discriminate|]. apply IH; [exact H| lia].
    - apply IH; [exact H| lia].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition JT : Z := 0x2100c.
Definition jt_bytes : list byte := match image_bytes bsegs JT 336 with Some bs => bs | None => [] end.

(* [comment removed for export] *)
Definition jt_off (c : Z) : Z :=
  if (c =? 34) || (c =? 47) || (c =? 92) then 0x645e4
  else if c =? 98 then 0x64630
  else if c =? 102 then 0x64650
  else if c =? 117 then 0x64670
  else if c =? 114 then 0x646d0
  else if c =? 110 then 0x646f0
  else if c =? 116 then 0x64710
  else 0x649d8.

Lemma jt_off_range : forall c, 0 <= jt_off c < 2^31.
Proof. intros c. unfold jt_off. repeat (destruct (_ : bool)); lia. Qed.

Lemma jt_bytes_ok : ro_bytes_b bsegs JT jt_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma jt_bytes_length : length jt_bytes = 336%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma jt_entry : forall k : nat, (k < 84)%nat ->
  firstn 4 (skipn (4 * k) jt_bytes) = le4 (Z_to_bv 64 (jt_off (34 + Z.of_nat k))).
Proof.
  intros k Hk. apply bytes_eq_of_unsigned.
  do 84 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma jt_read_k : forall m k, mem_inv bsegs m -> (k < 84)%nat ->
  ov_read_bytes bsegs m (wa (JT + Z.of_nat (4 * k))) 4 = Some (le4 (Z_to_bv 64 (jt_off (34 + Z.of_nat k)))).
Proof.
  intros m k MI Hk.
  pose proof (ro_bytes_at bsegs m JT jt_bytes MI ltac:(unfold JT; lia) ltac:(rewrite jt_bytes_length; unfold JT; lia)
                (ro_bytes_b_sound bsegs _ _ jt_bytes_ok)) as BY.
  rewrite (bytes_at_ov_read bsegs m JT jt_bytes (4 * k) 4 BY) by (rewrite jt_bytes_length; lia).
  rewrite (jt_entry k Hk). reflexivity.
Qed.

Lemma jt_read : forall m c, mem_inv bsegs m -> 34 <= c <= 117 ->
  ov_read_bytes bsegs m (wa (JT + 4 * (c - 34))) 4 = Some (le4 (Z_to_bv 64 (jt_off c))).
Proof.
  intros m c MI Hc.
  pose proof (jt_read_k m (Z.to_nat (c - 34)) MI ltac:(lia)) as H.
  replace (Z.of_nat (4 * Z.to_nat (c - 34))) with (4 * (c - 34)) in H by lia.
  replace (34 + Z.of_nat (Z.to_nat (c - 34))) with c in H by lia.
  exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma aclient_image_lt : forall a, aclient_image a -> 0 <= a < 0x5ff000.
Proof.
  intros a H. unfold aclient_image, AERRNO, ATP, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI in *.
  destruct H as [H|[H|(H & _ & _)]]; lia.
Qed.

(* [comment removed for export] *)
Lemma ppres_of_cj_pres : forall sp0 LR LB LF SP SP' P m m',
  cj_pres sp0 LB LF SP m m' -> SP <= SP' -> (forall b, In b LR -> In b LB) -> ppres sp0 LR LF SP' P m m'.
Proof.
  intros sp0 LR LB LF SP SP' P m m' H HS HL a Ha (Hc & _ & _). apply H; [exact Ha|].
  destruct Hc as [Hs|[Hi|[(A & n & Hin & Hr)|[Hf|Hsh]]]];
    [left; lia| right; left; exact Hi| right; right; left| right; right; right; left; exact Hf| do 4 right; exact Hsh].
  exists A, n. split; [apply HL; exact Hin| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ppres_of_munch : forall sp0 LR LF SP P W m m',
  munch W m m' -> wmono bsegs m m' ->
  (forall a, 0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> outside W a) -> ppres sp0 LR LF SP P m m'.
Proof. intros. eapply magree_of_munch; eauto. Qed.

Lemma ppres_weaken : forall sp0 LR LR' LF LF' SP SP' P m m',
  ppres sp0 LR LF SP P m m' -> SP <= SP' -> (forall b, In b LR' -> In b LR) -> (forall f, In f LF' -> In f LF) ->
  ppres sp0 LR' LF' SP' P m m'.
Proof.
  intros sp0 LR LR' LF LF' SP SP' P m m' H HS HL HF. eapply magree_mono; [exact H|].
  intros a (Hc & He & Hp). split; [| split; [exact He| exact Hp]].
  destruct Hc as [Hs|[Hi|[(A & n & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]];
    [left; lia| right; left; exact Hi| right; right; left| right; right; right; left| do 4 right; exact Hsh].
  - exists A, n. split; [apply HL; exact Hin| exact Hr].
  - exists Fr, k. split; [apply HF; exact Hin| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ppres_rw_cells_stack : forall sp0 LR LF SP P m m' A cs,
  ppres sp0 LR LF SP P m m' -> rw_cells bsegs m A cs -> SP <= A -> A + Z.of_nat (cells_size cs) <= sp0 + 4096 ->
  alloc_ceiling <= SP -> P + 56 <= alloc_ceiling ->
  rw_cells bsegs m' A cs.
Proof.
  intros sp0 LR LF SP P m m' A cs HP H HS HA HC HPc. eapply rw_cells_magree; [exact HP| exact H|].
  intros a Ha. split; [left; lia|]. unfold AERRNO, ATP. pose proof alloc_ceiling_eq. lia.
Qed.

Lemma ppres_stk : forall sp0 LR LF SP P m m' lo hi,
  ppres sp0 LR LF SP P m m' -> stk bsegs m lo hi -> SP <= lo -> hi <= sp0 + 4096 ->
  alloc_ceiling <= SP -> P + 56 <= alloc_ceiling -> stk bsegs m' lo hi.
Proof.
  intros sp0 LR LF SP P m m' lo hi HP ST HS Hh HC HPc. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  pose proof alloc_ceiling_eq.
  intros i Hi. destruct (HP i ltac:(lia) ltac:(split; [left; lia| unfold AERRNO, ATP; lia])) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma ppres_rw_cells_block : forall sp0 LR LF SP P m m' A cs B k,
  ppres sp0 LR LF SP P m m' -> rw_cells bsegs m A cs -> In (B, k) LR -> B <= A -> A + Z.of_nat (cells_size cs) <= B + k ->
  AIMG_HI <= B -> (B + k <= P \/ P + 56 <= B) ->
  rw_cells bsegs m' A cs.
Proof.
  intros sp0 LR LF SP P m m' A cs B k HP H Hin HB HA HH HD. eapply rw_cells_magree; [exact HP| exact H|].
  intros a Ha. split; [right; right; left; exists B, k; split; [exact Hin| lia]|]. unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. lia.
Qed.

Lemma ppres_bytes_at_block : forall sp0 LR LF SP P m m' A bs B k,
  ppres sp0 LR LF SP P m m' -> bytes_at bsegs m A bs -> In (B, k) LR -> B <= A -> A + Z.of_nat (length bs) <= B + k ->
  AIMG_HI <= B -> (B + k <= P \/ P + 56 <= B) ->
  bytes_at bsegs m' A bs.
Proof.
  intros sp0 LR LF SP P m m' A bs B k HP H Hin HB HA HH HD. eapply bytes_at_magree; [exact HP| exact H|].
  intros a Ha. split; [right; right; left; exists B, k; split; [exact Hin| lia]|]. unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ppres_cj_chain : forall sp0 LR LF SP P m m' T d p B,
  ppres sp0 LR LF SP P m m' -> cj_chain T m d p B -> (forall b, In b B -> In b LR) ->
  (forall A n, In (A, n) B -> AIMG_HI <= A /\ (A + n <= P \/ P + 56 <= A)) ->
  cj_chain T m' d p B.
Proof.
  intros sp0 LR LF SP P m m' T d p B HP H HB HR. eapply cj_chain_magree; [exact H| exact HP|].
  intros a (A & n & Hin & Ha). destruct (HR A n Hin) as [H1 H2].
  split; [right; right; left; exists A, n; split; [apply HB; exact Hin| exact Ha]|]. unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. lia.
Qed.

Lemma ppres_cj_str : forall sp0 LR LF SP P m m' s B,
  ppres sp0 LR LF SP P m m' -> cj_str m s B -> (forall b, In b B -> In b LR) ->
  (forall A n, In (A, n) B -> AIMG_HI <= A /\ (A + n <= P \/ P + 56 <= A)) -> cj_str m' s B.
Proof.
  intros sp0 LR LF SP P m m' s B HP H HB HR. eapply cj_str_magree; [exact HP| exact H|].
  intros a (A & n & Hin & Ha). destruct (HR A n Hin) as [H1 H2].
  split; [right; right; left; exists A, n; split; [apply HB; exact Hin| exact Ha]|]. unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ppres_pbuf_sh : forall sp0 LR LF SP P m m',
  ppres sp0 LR LF SP P m m' -> pbuf_sh m P -> In (P - 32, 1) LF -> AIMG_HI <= P -> P + 56 <= alloc_ceiling ->
  sclr P 56 ->                                   (* [comment removed for export] *)
  pbuf_sh m' P.
Proof.
  intros sp0 LR LF SP P m m' HP H Hin HH HC HB. eapply pbuf_sh_ext; [exact H|].
  intros j Hj. pose proof (SH_bounds P ltac:(unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HH; try rewrite alloc_ceiling_eq in HC; lia)).
  pose proof (SH_bounds (P + 55) ltac:(unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HH; try rewrite alloc_ceiling_eq in HC; lia)).
  destruct (HP j ltac:(lia)) as [E _]; [|exact E].
  split; [| unfold sclr, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; split; lia].
  right; right; right; left. exists (P - 32), 1. split; [exact Hin|]. right.
  change (fsz 1) with 128. pose proof (SH_mono (P - 32) P ltac:(lia)). pose proof (SH_aligned_add (P - 32) 128).
  unfold SH in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma gmono_refl : forall g, gmono g g.
Proof. intros g w H. exact H. Qed.
Lemma gmono_trans : forall g1 g2 g3, gmono g1 g2 -> gmono g2 g3 -> gmono g1 g3.
Proof. intros g1 g2 g3 H1 H2 w H. apply H2, H1, H. Qed.

(* [comment removed for export] *)
Lemma disjoint_from_In : forall W A n,
  (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n H; [exact I|]. cbn. split; [apply H; left; reflexivity|].
  apply IH. intros lo' hi' Hin. apply H. right. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma le1_lit : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_window : forall m A bs j n,
  bytes_at bsegs m A bs -> 0 <= j -> (Z.to_nat j + n <= length bs)%nat ->
  bytes_at bsegs m (A + j) (firstn n (skipn (Z.to_nat j) bs)).
Proof.
  intros m A bs j n BY Hj Hn.
  rewrite <- (firstn_skipn (Z.to_nat j) bs) in BY. apply bytes_at_app in BY. destruct BY as [_ BY].
  rewrite length_firstn, Nat.min_l in BY by lia. replace (A + Z.of_nat (Z.to_nat j)) with (A + j) in BY by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat j) bs)) in BY. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY.
Qed.

Lemma firstn_skipn_length : forall {X} (l : list X) j n, (j + n <= length l)%nat -> length (firstn n (skipn j l)) = n.
Proof. intros X l j n H. rewrite length_firstn, length_skipn. lia. Qed.

(* [comment removed for export] *)
Lemma text_read : forall m A bs i a,
  bytes_at bsegs m A bs -> 0 <= i -> (Z.to_nat i < length bs)%nat -> a = wa (A + i) ->
  exists b, nth_error bs (Z.to_nat i) = Some b /\ ov_read_bytes bsegs m a 1 = Some [b] /\ at_ bs i = bv_unsigned b.
Proof.
  intros m A bs i a BY Hi Hl ->. destruct (nth_error_lt_some bs (Z.to_nat i) Hl) as [b Hb].
  exists b. split; [exact Hb|]. split; [| unfold at_; rewrite Hb; reflexivity].
  eapply u8ro_read; [exact BY| exact Hb| exact Hi| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma jt_read' : forall m c, mem_inv bsegs m -> 34 <= c <= 117 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftl (c + -34) 2 + JT)) 4 = Some (le4 (Z_to_bv 64 (jt_off c))).
Proof.
  intros m c MI Hc. rewrite <- (jt_read m c MI Hc). unfold wa. do 2 f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma srliw_small : forall x k, 0 <= x < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = x / 2^k.
Proof.
  intros x k Hx Hk. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= x / 2^k <= x). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_lts_small : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma land_hi10 : forall F0 : Z, 0 <= F0 < 2^64 -> Z.land F0 18446744073709550592 = F0 - F0 mod 1024.
Proof.
  intros F0 H.
  assert (E : 18446744073709550592 = Z.lxor (Z.ones 64) (Z.ones 10)) by reflexivity. rewrite E.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lxor_spec, !Z.testbit_ones_nonneg by lia.
  replace (F0 - F0 mod 1024) with (Z.shiftl (Z.shiftr F0 10) 10).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change 1024 with (2^10). rewrite Z.mod_eq by lia. lia. }
  rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec n 10); destruct (Z.ltb_spec n 64); cbn [xorb andb].
  - rewrite (Z.testbit_neg_r _ (n - 10)) by lia. apply andb_false_r.
  - lia.
  - rewrite Z.shiftr_spec by lia. rewrite andb_true_r. f_equal. lia.
  - rewrite andb_false_r. symmetry. rewrite Z.shiftr_spec by lia. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec F0 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma lor_bound : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb. assert (Hn : 0 <= n). { destruct (Z.neg_nonneg_cases n); [|lia]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
  assert (Z.lor a b <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). pose proof (Z.lor_nonneg a b).
  apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HeapStores.
  Variable AI : art_iface.

  (* [comment removed for export] *)
  Lemma ppres_frame_store : forall sp0 SPB LB LF TRS BB m0 mo g LR SP P lo' hi' m1 m2,
    ART AI sp0 SPB LB LF TRS BB m0 mo g -> (forall b, In b LR -> In b LB) ->
    munch [(lo', hi')] m1 m2 -> wmono bsegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP -> sp0 <= 2^47 ->
    ppres sp0 LR LF SP P m1 m2.
  Proof.
    intros sp0 SPB LB LF TRS BB m0 mo g LR SP P lo' hi' m1 m2 HL HLR MU WM Hlo Hhi H47 a Ha (Hp & _ & _).
    try rewrite alloc_ceiling_eq in Hlo.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hp as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4). try rewrite alloc_ceiling_eq in R4. lia.
    - pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _).
      try rewrite alloc_ceiling_eq in HF2. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in HF1. bandM. sepM.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      unfold SH, SHADOW_OFFSET in Hr. Z.div_mod_to_equations. lia.
    - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ppres_pbuf_store : forall sp0 LR LF SP P lo' hi' m1 m2,
    munch [(lo', hi')] m1 m2 -> wmono bsegs m1 m2 -> P <= lo' -> hi' <= P + 56 ->
    ppres sp0 LR LF SP P m1 m2.
  Proof.
    intros sp0 LR LF SP P lo' hi' m1 m2 MU WM Hlo Hhi a Ha (_ & _ & Hx).
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ppres_block_store : forall sp0 SPB LBX LF TRS BB m0 mo g A n R LR SP P lo' hi' m1 m2,
    ART AI sp0 SPB LBX LF TRS BB m0 mo g -> Permutation ((A, n) :: R) LBX -> (forall b, In b LR -> In b R) ->
    alloc_ceiling <= SP -> sp0 <= 2^47 ->
    munch [(lo', hi')] m1 m2 -> wmono bsegs m1 m2 -> A <= lo' -> hi' <= A + n ->
    ppres sp0 LR LF SP P m1 m2.
  Proof.
    intros sp0 SPB LBX LF TRS BB m0 mo g A n R LR SP P lo' hi' m1 m2 HL HP HLR HSP H47 MU WM Hlo Hhi a Ha (Hc & _ & _).
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & R2 & R3 & R4).
    (* [comment removed for export] *)
    pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP))) as BND.
    pose proof alloc_ceiling_range as CR.
    try rewrite alloc_ceiling_eq in *. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in BND. bandM. sepM.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ D]. lia.
    - pose proof (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & _ & HF1 & HF2 & _ & _ & _ & HD).
      try rewrite alloc_ceiling_eq in HF2. unfold AIMG_HI in HF1.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct (HD A n (perm_in_head _ _ _ HP)) as [D|D]; destruct BND as [BND|BND];
        unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; Z.div_mod_to_equations; lia.
    - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh.
      destruct BND as [BND|BND]; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma art_frame_store : forall sp0 SPB LB LF TRS BB m mo g lo' hi' m',
    ART AI sp0 SPB LB LF TRS BB m mo g -> munch [(lo', hi')] m m' -> wmono bsegs m m' -> alloc_ceiling <= lo' -> hi' <= SPB ->
    ART AI sp0 SPB LB LF TRS BB m' mo g.
  Proof. intros. eapply (art_frame AI); eauto. constructor; [|constructor]. right; left. cbn. lia. Qed.

  Lemma art_block_store : forall sp0 SPB LB LF TRS BB m mo g A n lo' hi' m',
    ART AI sp0 SPB LB LF TRS BB m mo g -> In (A, n) LB -> munch [(lo', hi')] m m' -> wmono bsegs m m' -> A <= lo' -> hi' <= A + n ->
    ART AI sp0 SPB LB LF TRS BB m' mo g.
  Proof. intros. eapply (art_frame AI); eauto. constructor; [|constructor]. do 7 right. left. exists A, n. cbn. auto. Qed.

  (* [comment removed for export] *)
  Lemma art_pbuf_store : forall sp0 SPB LB LF TRS BB m mo g P lo' hi' m',
    ART AI sp0 SPB LB LF TRS BB m mo g -> In (P - 32, 1) LF -> munch [(lo', hi')] m m' -> wmono bsegs m m' ->
    P <= lo' -> hi' <= P + 56 ->
    ART AI sp0 SPB LB LF TRS BB m' mo g.
  Proof.
    intros. eapply (art_frame AI); eauto. constructor; [|constructor]. do 8 right. left.
    exists (P - 32), 1. split; [assumption|]. cbn. change (fsz 1) with 128. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ACJST_high_store : forall m m' lo' hi',
    ACJST m -> munch [(lo', hi')] m m' -> wmono bsegs m m' -> AIMG_HI <= lo' -> ACJST m'.
  Proof.
    intros m m' lo' hi' CJ MU WM Hlo. eapply ACJST_high; [exact CJ| exact MU| exact WM|].
    intros lo hi Hin. destruct Hin as [E|[]]. inversion E; subst. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma errno_high_store : forall m m' lo' hi' errv,
    rw_cells bsegs m AERRNO [C4 errv] -> munch [(lo', hi')] m m' -> wmono bsegs m m' -> AIMG_HI <= lo' ->
    rw_cells bsegs m' AERRNO [C4 errv].
  Proof.
    intros m m' lo' hi' errv H MU WM Hlo. eapply rw_cells_transport; [exact H| exact MU| exact WM|].
    cbn. unfold AERRNO, ATP, AIMG_HI in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pbuf_sh_high_store : forall m m' lo' hi' P,
    pbuf_sh m P -> munch [(lo', hi')] m m' -> sclr lo' (hi' - lo') -> AIMG_HI <= P -> P + 56 <= alloc_ceiling ->
    pbuf_sh m' P.
  Proof.
    intros m m' lo' hi' P H MU Hlo HP HC. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. try rewrite alloc_ceiling_eq in HC.
    eapply pbuf_sh_munch; [exact H| exact MU| lia| lia|].
    cbn. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
  Qed.

  Lemma text_sh_high_store : forall m m' lo' hi' CA blen,
    text_sh m CA blen -> munch [(lo', hi')] m m' -> sclr lo' (hi' - lo') -> 0 <= CA -> CA + blen <= alloc_ceiling ->
    text_sh m' CA blen.
  Proof.
    intros m m' lo' hi' CA blen H MU Hlo H0 HC. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. try rewrite alloc_ceiling_eq in HC.
    eapply text_sh_munch; [exact H| exact MU| lia| lia|].
    cbn. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
  Qed.

  Lemma shadow_ok_high_store : forall m m' lo' hi' A n,
    shadow_ok m A n -> munch [(lo', hi')] m m' -> 0 < n -> sclr lo' (hi' - lo') -> 0 <= A -> A + n <= alloc_ceiling ->
    shadow_ok m' A n.
  Proof.
    intros m m' lo' hi' A n H MU Hn Hlo H0 HC. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. try rewrite alloc_ceiling_eq in HC.
    eapply shadow_ok_munch; [exact H| exact MU| exact Hn| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                             | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia|].
    cbn. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia.
  Qed.

  Lemma shbase_cells_high_store : forall m m' lo' hi',
    shbase_cells m -> munch [(lo', hi')] m m' -> AIMG_HI <= lo' -> shbase_cells m'.
  Proof.
    intros m m' lo' hi' H MU Hlo. unfold AIMG_HI in Hlo. eapply shbase_cells_munch; [exact H| exact MU| cbn; lia| cbn; lia].
  Qed.
End HeapStores.

(* [comment removed for export] *)
Lemma cb_remove_head : forall A n LB, cb_remove A ((A, n) :: LB) = LB.
Proof. intros. cbn. rewrite Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma split_first_nul : forall (l : list byte) i, nth_error l i = Some (wb 0) ->
  exists str tail, l = str ++ wb 0 :: tail /\ ~ In (wb 0) str.
Proof.
  induction l as [|b l IH]; intros i H; [destruct i; discriminate|].
  destruct (bv_eq_dec 8 b (wb 0)) as [->|NE].
  - exists [], l. split; [reflexivity| intros []].
  - destruct i as [|i]; cbn in H; [inversion H; subst; exfalso; apply NE; reflexivity|].
    destruct (IH i H) as (str & tail & -> & NI). exists (b :: str), tail. split; [reflexivity|].
    intros [E|Hin]; [apply NE; exact E| exact (NI Hin)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FromART.
  Variable AI : art_iface.

  Lemma art_shbase : forall sp0 SPB LB LF TRS BB m mo g, ART AI sp0 SPB LB LF TRS BB m mo g -> shbase_cells m.
  Proof. intros. destruct (art_rtcells AI _ _ _ _ _ _ _ _ _ H) as ([G1 G2] & _). split; assumption. Qed.

  Lemma art_text_sh : forall sp0 SPB LB LF TRS BB m mo g D n CA blen,
    ART AI sp0 SPB LB LF TRS BB m mo g -> In (D, n) LB -> D <= CA -> CA + blen <= D + n -> text_sh m CA blen.
  Proof.
    intros sp0 SPB LB LF TRS BB m mo g D n CA blen H Hin H1 H2.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ H Hin) as [_ SO]. eapply text_sh_of_shadow_ok; eauto.
  Qed.

  Lemma art_block_shadow_ok : forall sp0 SPB LB LF TRS BB m mo g A n,
    ART AI sp0 SPB LB LF TRS BB m mo g -> In (A, n) LB -> shadow_ok m A n.
  Proof. intros. eapply (art_shadow AI); eauto. Qed.
End FromART.


End CeilWrap.
End CJ_parse_lemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow.
Import CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_tree CJ_conv.
Import CJ_parse_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section T.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 m1 : word -> option byte) (A lo : Z) (c0 c1 c2 c3 : byte) (j8 : list byte).
  (* [comment removed for export] *)
  Hypothesis RO : ro_cells bsegs m1 A [C1 c0; C1 c1; C1 c2; C1 c3].
  Hypothesis MI : mem_inv bsegs m1.
  Hypothesis FR : rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 j8; C8 ra].
  Hypothesis STK : stk bsegs m1 lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(lo, bv_unsigned sp)] m0 m1.
  Hypothesis WM : wmono bsegs m0 m1.
  Hypothesis BY1 : bytes_at bsegs m1 A [c0; c1; c2; c3].
  Hypothesis SB1 : shbase_cells m1.
  Hypothesis TS1 : text_sh m1 A 4.
  Hypothesis AHI : A + 4 <= alloc_ceiling.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOR : lo + 16 <= bv_unsigned sp.

  Notation SP := (bv_unsigned sp) (only parsing).
  Notation ST pc x5 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs)) (only parsing).
  Notation POST := (hex4_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A [c0;c1;c2;c3] lo m0) (only parsing).
  Notation K0 := (bv_unsigned c0) (only parsing).
  Notation K1 := (bv_unsigned c1) (only parsing).
  Notation K2 := (bv_unsigned c2) (only parsing).
  Notation K3 := (bv_unsigned c3) (only parsing).
  Notation L z := (Z_to_bv 64 z) (only parsing).
  Notation BASE := (Z_to_bv 64 2147450880) (only parsing).

  Lemma AB : 0 <= A /\ A + 4 <= 2^64.
  Proof. pose proof (ro_cells_bound bsegs _ _ _ RO) as B. cbn [cells_size Cells.csize Nat.add] in B. lia. Qed.
  Lemma R0 : 0 <= K0 < 256. Proof. pose proof (bv_unsigned_in_range 8 c0) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma R1 : 0 <= K1 < 256. Proof. pose proof (bv_unsigned_in_range 8 c1) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma R2 : 0 <= K2 < 256. Proof. pose proof (bv_unsigned_in_range 8 c2) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma R3 : 0 <= K3 < 256. Proof. pose proof (bv_unsigned_in_range 8 c3) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma SPR : 0 <= bv_unsigned sp < 2^64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2^64) in R. lia. Qed.

  Ltac pre := intros; pose proof AB; pose proof R0; pose proof R1; pose proof R2; pose proof R3; pose proof SPR;
              pose proof AHI as AHI'; pose proof LOC as LOC'; try rewrite alloc_ceiling_eq in AHI', LOC'.
  Ltac ml := Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Lemma post_ok : forall (h : Z) x5 x11 x12 x13 x14 x15 x16 x17,
    0 <= h < 2^16 ->
    evt bsegs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (L h) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m1 (seg_rom bsegs)).
  Proof.
    intros. apply evt_done. unfold hex4_post. do 9 eexists. exists m1, h. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { pose proof SPR. pose proof FR as FR'. pose proof STK as ST'. release_frame FR' ST' (bv_unsigned sp). exact ST'. }
    split; [exact BY1| assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma L_fail : forall x5 x10 x11 x12 x13 x14 x15 x16 x17,
    evt bsegs POST (ST 0x86574 x5 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof. pre. zstep. zstep. zstep. zstep. eapply post_ok. lia. Qed.

  (* [comment removed for export] *)
  Lemma L_comb : forall (J0 J1 J2 J3 : Z) x5,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 -> 0 <= K3 + J3 <= 15 ->
    evt bsegs POST (ST 0x86540 x5 (L K3) (L K2) (L K0) (L J0) (L J3) (L K1) (L J1) (L J2)).
  Proof.
    pre. do 10 zstep. zstep. zstep. zstep.
    eapply post_ok. rewrite ?zb_shiftl_mul by lia. ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_c3 : forall (J0 J1 J2 : Z) x5 x14,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 ->
    evt bsegs POST (ST 0x864cc x5 (L (A + 3)) (L K2) (L K0) (L J0) x14 (L K1) (L J1) (L J2)).
  Proof.
    pre. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
    - zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_fail|]. zstep. apply L_comb; ml.
      + zstep. zstep. apply L_comb; ml.
    - zstep. zstep. apply L_comb; ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_c3chk : forall (J0 J1 J2 : Z) x5,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 ->
    evt bsegs POST (ST 0x864b8 x5 (L A) (L K2) (L K0) (L J0) BASE (L K1) (L J1) (L J2)).
  Proof.
    pre. zstep; zstep; zstep; pose proof (TS1 (A + 3) ltac:(lia)) as CK; asan_chk CK; apply L_c3; ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_c2 : forall (J0 J1 : Z) x5 x17,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 ->
    evt bsegs POST (ST 0x8649c x5 (L A) (L (A + 2)) (L K0) (L J0) BASE (L K1) (L J1) x17).
  Proof.
    pre. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
    - zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_fail|].
        zstep. zstep. zstep. if_cases G; zify_cond G; [apply L_c3chk; ml| exfalso; lia].
      + zstep. zstep. zstep. if_cases G; zify_cond G; [apply L_c3chk; ml| exfalso; lia].
    - zstep. zstep. zstep. if_cases G; zify_cond G; [exfalso; lia| apply L_c3chk; ml].
  Qed.

  (* [comment removed for export] *)
  Lemma L_c2chk : forall (J0 J1 : Z) x5 x11 x17,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 ->
    evt bsegs POST (ST 0x86488 x5 (L A) x11 (L K0) (L J0) BASE (L K1) (L J1) x17).
  Proof.
    pre. zstep; zstep; zstep; pose proof (TS1 (A + 2) ltac:(lia)) as CK; asan_chk CK; apply L_c2; ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_c1 : forall (J0 : Z) x5 x15 x16 x17,
    0 <= K0 + J0 <= 15 ->
    evt bsegs POST (ST 0x86434 x5 (L A) (L (A + 1)) (L K0) (L J0) BASE x15 x16 x17).
  Proof.
    pre. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
    - zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_fail|].
        zstep. zstep. zstep. if_cases G; zify_cond G; [exfalso; lia| apply L_c2chk; ml].
      + zstep. zstep. zstep. if_cases G; zify_cond G; [apply L_c2chk; ml| exfalso; lia].
    - zstep. zstep. zstep. if_cases G; zify_cond G; [apply L_c2chk; ml| exfalso; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma L_c1chk : forall (J0 : Z) x5 x11 x15 x16 x17,
    0 <= K0 + J0 <= 15 ->
    evt bsegs POST (ST 0x86420 x5 (L A) x11 (L K0) (L J0) BASE x15 x16 x17).
  Proof.
    pre. zstep; zstep; zstep; pose proof (TS1 (A + 1) ltac:(lia)) as CK; asan_chk CK; apply L_c1; ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_c0 : forall x5 x11 x12 x13 x15 x16 x17,
    evt bsegs POST (ST 0x863cc x5 (L A) x11 x12 x13 BASE x15 x16 x17).
  Proof.
    pre. zstep. zstep. zstep. zstep. if_cases Ka; zify_cond Ka.
    - zstep. zstep. zstep. if_cases Kb; zify_cond Kb.
      + zstep. zstep. zstep. if_cases Kc; zify_cond Kc; [apply L_fail|].
        zstep. zstep. zstep. if_cases G; zify_cond G; [exfalso; lia| apply L_c1chk; ml].
      + zstep. zstep. zstep. if_cases G; zify_cond G; [apply L_c1chk; ml| exfalso; lia].
    - zstep. zstep. zstep. if_cases G; zify_cond G; [apply L_c1chk; ml| exfalso; lia].
  Qed.
End T.

Lemma hex4_spec : hex4_stmt.
Proof.
  unfold hex4_stmt. intros until b4. intros BY LEN AHI SB TSH MI ST LOC LOR A0. unfold PARSE_HEX4, PARSE_HEX4_STACK in *. subst a0.
  destruct b4 as [|c0 [|c1 [|c2 [|c3 [|]]]]]; cbn in LEN; try discriminate.
  pose proof (bytes_at_bound _ _ _ _ BY) as ABD. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in ABD.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof AHI as AHI'. pose proof LOC as LOC'. try rewrite alloc_ceiling_eq in AHI', LOC'.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof SB as SB0. shbase_split SB0.
  carve_frame 16%nat ST.
  zstep. zstep.                                          (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SB1 : shbase_cells mx) by (split; assumption);
    assert (TS1 : text_sh mx A 4)
      by (eapply text_sh_munch; [exact TSH| exact MU| lia| lia| cbn; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia]);
    assert (RO : ro_cells bsegs mx A [C1 c0; C1 c1; C1 c2; C1 c3])
      by (split; [cbn; repeat split; exact I| cbn; rewrite ?app_nil_r; exact BY])
  end.
  zstep. zstep. zstep.                                   (* [comment removed for export] *)
  zstep. zstep.                                          (* [comment removed for export] *)
  pose proof (TS1 A ltac:(lia)) as CK. asan_chk CK.     (* [comment removed for export] *)
  eapply L_c0; eassumption.
Qed.


End CeilWrap.
