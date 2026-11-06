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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
Module CJ_pbuf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Definition pbuf_cells (content length offset depth : Z) : list cell :=
  [C8 (wz content); C8 (wz length); C8 (wz offset); C8 (wz depth); C8 (wz PMALLOC); C8 (wz PFREE); C8 (wz PREALLOC)].

Definition pbuf_at (m : word -> option byte) (P content length offset depth : Z) : Prop :=
  rw_cells usegs m P (pbuf_cells content length offset depth).

Lemma pbuf_cells_size : forall c l o d, cells_size (pbuf_cells c l o d) = 56%nat.
Proof. reflexivity. Qed.

Lemma pbuf_at_bound : forall m P c l o d, pbuf_at m P c l o d -> 0 <= P /\ P + 56 <= 2^64.
Proof. intros. pose proof (rw_cells_bound usegs _ _ _ H) as HB. rewrite pbuf_cells_size in HB. lia. Qed.

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
End CJ_pbuf.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_tree.
Module CJ_parse_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree CJ_pbuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PARSE_HEX4   : Z := 0x153f8.
Definition PARSE_STRING : Z := 0x14c2c.
Definition PARSE_VALUE  : Z := 0x13b50.
Definition PARSE_OBJECT : Z := 0x15040.
Definition PARSE_WLOPTS : Z := 0x138d0.   (* [comment removed for export] *)
Definition PARSE_WOPTS  : Z := 0x1387c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PARSE_STRING_STACK : Z := 128 + RMALLOC_STACK.                  (* [comment removed for export] *)
Definition PARSE_STACK (depth : Z) : Z := 144 * (1001 - depth) + 16384.    (* [comment removed for export] *)
Definition PARSE_DOC_STACK : Z := 112 + PARSE_STACK 0.                     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition Fagree (F F' : bvmap 5 word) : Prop :=
  forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k.

Lemma Fagree_refl : forall F, Fagree F F.
Proof. intros F k _ _ _. reflexivity. Qed.
Lemma Fagree_trans : forall F1 F2 F3, Fagree F1 F2 -> Fagree F2 F3 -> Fagree F1 F3.
Proof. intros F1 F2 F3 H1 H2 k A B C. rewrite (H2 k A B C). apply H1; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pv_addr (LR : list cblock) (SP P : Z) (a : Z) : Prop :=
  (SP <= a /\ ~ (P <= a < P + 56)) \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a) \/ in_cblock LR a.
Definition ppres (LR : list cblock) (SP P : Z) (m m' : word -> option byte) : Prop := magree (pv_addr LR SP P) m m'.

(* [comment removed for export] *)
Definition doc_addr (LB : list cblock) (SP : Z) (a : Z) : Prop :=
  cj_client_addr LB SP a /\ ~ (PGERROR <= a < PGERROR + 16).
Definition dpres (LB : list cblock) (SP : Z) (m m' : word -> option byte) : Prop := magree (doc_addr LB SP) m m'.

Lemma ppres_refl : forall LR SP P m, ppres LR SP P m m.
Proof. intros; apply magree_refl. Qed.
Lemma ppres_trans : forall LR SP P m1 m2 m3, ppres LR SP P m1 m2 -> ppres LR SP P m2 m3 -> ppres LR SP P m1 m3.
Proof. intros; eapply magree_trans; eauto. Qed.
Lemma dpres_refl : forall LB SP m, dpres LB SP m m.
Proof. intros; apply magree_refl. Qed.
Lemma dpres_trans : forall LB SP m1 m2 m3, dpres LB SP m1 m2 -> dpres LB SP m2 m3 -> dpres LB SP m1 m3.
Proof. intros; eapply magree_trans; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition parse_inv (HI : cj_heap_iface) (m : word -> option byte) (mo : Model) (SPB : Z) (LB X LR : list cblock)
    (U P CA blen : Z) (bs : list byte) (D n lo SP : Z) (errv : word) : Prop :=
  LHEAP HI SPB LB m mo
  /\ Permutation ((U, 64) :: X ++ LR) LB
  /\ In (D, n) LR /\ D <= CA /\ CA + blen <= D + n
  /\ bytes_at usegs m CA bs /\ Z.of_nat (length bs) = blen /\ blen < 2^31
  /\ CJST m
  /\ rw_cells usegs m PERRNO [C4 errv]
  /\ mem_inv usegs m
  /\ stk usegs m lo SP /\ alloc_ceiling <= lo
  /\ SP <= P /\ P + 56 <= SPB /\ SPB < 2^62
  /\ P mod 8 = 0.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hex4_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (b4 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 a1 a2 a3 a4 a5 a6 a7 : word) (m' : word -> option byte) (h : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' A b4
    /\ 0 <= h < 2^16.

Definition hex4_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (b4 : list byte),
  bytes_at usegs m A b4 -> length b4 = 4%nat ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A ->
  evt usegs (hex4_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A b4 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PARSE_HEX4) fc None m (seg_rom usegs)).

Section S.
  Variable HI : cj_heap_iface.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition parse_string_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SPB : Z) (LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (m : word -> option byte)
      (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                          (r : Z) (off' : Z) (LB' X : list cblock) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ a0 = wz r
      /\ parse_inv HI m' mo' SPB LB' X LR U P CA blen bs D n lo (bv_unsigned sp) errv'
      /\ ppres LR (bv_unsigned sp) P m m'
      /\ pbuf_at m' P CA blen off' depth /\ off <= off' <= blen
      /\ ( (r = 0 /\ X = [] /\ rw_cells usegs m' U (node_cells nx pv ch ty p1 vs vi p2 vd ky))
           \/ (r = 1 /\ exists (S k : Z), X = [(S, k)] /\ S <> 0
                 /\ rw_cells usegs m' U (node_cells nx pv ch 16 p1 S vi p2 vd ky)
                 /\ cj_str m' S [(S, k)]) ).

  Definition parse_string_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (errv : word)
           (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z),
      parse_inv HI m mo SPB LB [] LR U P CA blen bs D n lo (bv_unsigned sp) errv ->
      rw_cells usegs m U (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
      pbuf_at m P CA blen off depth -> 0 <= off < blen ->
      lo <= bv_unsigned sp - PARSE_STRING_STACK ->
      tp = wz PTP -> a0 = wz U -> a1 = wz P ->
      SCPS usegs (parse_string_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LR U P CA blen off depth bs D n lo m
                    nx pv ch ty p1 vs vi p2 vd ky)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_STRING) fc None m (seg_rom usegs)) mo.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition parse_value_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (m : word -> option byte)
      (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (r : Z) (off' depth' : Z) (LB' X : list cblock) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ a0 = wz r
      /\ Fagree F F' /\ frm0 fc'
      /\ parse_inv HI m' mo' SPB LB' X LR U P CA blen bs D n lo (bv_unsigned sp) errv'
      /\ ppres LR (bv_unsigned sp) P m m'
      /\ pbuf_at m' P CA blen off' depth'
      /\ ( (r = 0 /\ X = [] /\ rw_cells usegs m' U (node_cells nx pv 0 ty p1 0 vi p2 vd ky))
           \/ (r = 1 /\ depth' = depth /\ off <= off' <= blen
               /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                    X = Bv ++ Bc
                    /\ rw_cells usegs m' U (node_cells nx pv ch ty' p1 vs vi' p2 vd' ky)
                    /\ CJ_PRINTABLE ty'
                    /\ cj_str m' vs Bv
                    /\ cj_chain CJ_PRINTABLE m' dc ch Bc
                    /\ Z.of_nat dc + depth <= 1000) ).

  (* [comment removed for export] *)
  Definition parse_value_at (nfuel : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (errv : word)
           (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z),
      parse_inv HI m mo SPB LB [] LR U P CA blen bs D n lo (bv_unsigned sp) errv ->
      rw_cells usegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      pbuf_at m P CA blen off depth -> 0 <= off <= blen -> 0 <= depth <= 1000 ->
      blen - off <= Z.of_nat nfuel ->
      lo <= bv_unsigned sp - PARSE_STACK depth ->
      frm0 fc -> tp = wz PTP -> a0 = wz U -> a1 = wz P ->
      SCPS usegs (parse_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR U P CA blen off depth bs D n lo m
                    nx pv ty p1 vi p2 vd ky)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_VALUE) fc None m (seg_rom usegs)) mo.

  Definition parse_value_stmt : Prop := forall nfuel, parse_value_at nfuel.

  (* [comment removed for export] *)
  Definition parse_object_at (nfuel : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR : list cblock) (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z) (errv : word)
           (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z),
      parse_inv HI m mo SPB LB [] LR U P CA blen bs D n lo (bv_unsigned sp) errv ->
      rw_cells usegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      pbuf_at m P CA blen off depth -> 0 <= off <= blen -> 0 <= depth <= 1000 ->
      blen - off <= Z.of_nat nfuel ->
      lo <= bv_unsigned sp - PARSE_STACK depth ->
      frm0 fc -> tp = wz PTP -> a0 = wz U -> a1 = wz P ->
      SCPS usegs (parse_value_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR U P CA blen off depth bs D n lo m
                    nx pv ty p1 vi p2 vd ky)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_OBJECT) fc None m (seg_rom usegs)) mo.

  Definition parse_object_stmt : Prop := forall nfuel, parse_object_at nfuel.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition parse_doc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LB : list cblock) (CA : Z) (bs : list byte) (lo : Z) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (r : Z) (LB' : list cblock) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ a0 = wz r
      /\ Fagree F F' /\ frm0 fc'
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ CJST m' /\ rw_cells usegs m' PERRNO [C4 errv']
      /\ LHEAP HI SPB LB' m' mo'
      /\ bytes_at usegs m' CA bs
      /\ dpres LB (bv_unsigned sp) m m'
      /\ ( (r = 0 /\ Permutation LB' LB)
           \/ (r <> 0 /\ exists (B : list cblock) (d : nat) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word),
                 cj_chain CJ_PRINTABLE m' d r B /\ (d <= 1001)%nat
                 /\ Permutation LB' (B ++ LB)
                 /\ rw_cells usegs m' r (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0)) ).

  Definition parse_wlopts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB : list cblock) (CA blen : Z) (bs : list byte) (D n lo : Z) (errv : word),
      LHEAP HI SPB LB m mo ->
      In (D, n) LB -> D <= CA -> CA + blen <= D + n -> 0 < CA ->
      bytes_at usegs m CA bs -> Z.of_nat (length bs) = blen -> blen < 2^31 ->
      CJST m -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m ->
      stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PARSE_DOC_STACK ->
      bv_unsigned sp <= SPB -> SPB < 2^62 -> bv_unsigned sp mod 16 = 0 ->   (* [comment removed for export] *)
      frm0 fc -> tp = wz PTP ->
      a0 = wz CA -> a1 = wz blen -> a2 = wz 0 ->
      SCPS usegs (parse_doc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LB CA bs lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_WLOPTS) fc None m (seg_rom usegs)) mo.

  (* [comment removed for export] *)
  Definition parse_wopts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB : list cblock) (V : Z) (str slack : list byte) (D n lo : Z) (errv : word),
      LHEAP HI SPB LB m mo ->
      In (D, n) LB -> D <= V -> V + Z.of_nat (length str) + 1 <= D + n -> 0 < V ->
      bytes_at usegs m V (str ++ wb 0 :: slack) -> ~ In (wb 0) str -> Z.of_nat (length str) + 1 < 2^31 ->
      (- (V + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
      CJST m -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m ->
      stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PARSE_DOC_STACK ->
      bv_unsigned sp <= SPB -> SPB < 2^62 -> bv_unsigned sp mod 16 = 0 ->   (* [comment removed for export] *)
      frm0 fc -> tp = wz PTP ->
      a0 = wz V -> a1 = wz 0 ->
      SCPS usegs (parse_doc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LB V (str ++ [wb 0]) lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PARSE_WOPTS) fc None m (seg_rom usegs)) mo.

End S.


End CeilWrap.
End CJ_parse_iface.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
Module CJ_parse_lemmas.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree CJ_pbuf CJ_parse_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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

Definition JT : Z := 0x10620.
Definition jt_bytes : list byte := match image_bytes usegs JT 336 return list byte with Some bs => bs | None => [] end.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition jt_off (c : Z) : Z :=
  if (c =? 34) || (c =? 47) || (c =? 92) then 0x4794
  else if c =? 98 then 0x47c0
  else if c =? 102 then 0x47d0
  else if c =? 117 then 0x47e0
  else if c =? 114 then 0x4838
  else if c =? 110 then 0x4848
  else if c =? 116 then 0x4858
  else 0x49c0.

Lemma jt_off_range : forall c, 0 <= jt_off c < 2^31.
Proof. intros c. unfold jt_off. repeat (destruct (_ : bool)); lia. Qed.

Lemma jt_bytes_ok : ro_bytes_b usegs JT jt_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma jt_bytes_length : length jt_bytes = 336%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma jt_entry : forall k : nat, (k < 84)%nat ->
  firstn 4 (skipn (4 * k) jt_bytes) = le4 (Z_to_bv 64 (jt_off (34 + Z.of_nat k))).
Proof.
  intros k Hk. apply bytes_eq_of_unsigned.
  do 84 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma jt_read_k : forall m k, mem_inv usegs m -> (k < 84)%nat ->
  ov_read_bytes usegs m (wa (JT + Z.of_nat (4 * k))) 4 = Some (le4 (Z_to_bv 64 (jt_off (34 + Z.of_nat k)))).
Proof.
  intros m k MI Hk.
  pose proof (ro_bytes_at usegs m JT jt_bytes MI ltac:(unfold JT; lia) ltac:(rewrite jt_bytes_length; unfold JT; lia)
                (ro_bytes_b_sound usegs _ _ jt_bytes_ok)) as BY.
  rewrite (bytes_at_ov_read usegs m JT jt_bytes (4 * k) 4 BY) by (rewrite jt_bytes_length; lia).
  rewrite (jt_entry k Hk). reflexivity.
Qed.

Lemma jt_read : forall m c, mem_inv usegs m -> 34 <= c <= 117 ->
  ov_read_bytes usegs m (wa (JT + 4 * (c - 34))) 4 = Some (le4 (Z_to_bv 64 (jt_off c))).
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
Lemma ppres_of_cj_pres : forall LR LB SP SP' P m m',
  cj_pres LB SP m m' -> SP <= SP' -> (forall b, In b LR -> In b LB) -> ppres LR SP' P m m'.
Proof.
  intros LR LB SP SP' P m m' H HS HL a Ha Hp. apply H; [exact Ha|].
  destruct Hp as [[H1 _]|[H2|(A & n & Hin & Hr)]]; [left; lia| right; left; exact H2| right; right].
  exists A, n. split; [apply HL; exact Hin| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ppres_of_munch : forall LR SP P W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> pv_addr LR SP P a -> outside W a) -> ppres LR SP P m m'.
Proof. intros. eapply magree_of_munch; eauto. Qed.

Lemma ppres_weaken : forall LR LR' SP SP' P m m',
  ppres LR SP P m m' -> SP <= SP' -> (forall b, In b LR' -> In b LR) -> ppres LR' SP' P m m'.
Proof.
  intros LR LR' SP SP' P m m' H HS HL. eapply magree_mono; [exact H|].
  intros a [[H1 H2]|[H2|(A & n & Hin & Hr)]]; [left; split; [lia| exact H2]| right; left; exact H2| right; right].
  exists A, n. split; [apply HL; exact Hin| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ppres_rw_cells_stack : forall LR SP P m m' A cs,
  ppres LR SP P m m' -> rw_cells usegs m A cs -> SP <= A ->
  (A + Z.of_nat (cells_size cs) <= P \/ P + 56 <= A) -> rw_cells usegs m' A cs.
Proof.
  intros LR SP P m m' A cs HP H HS HD. eapply rw_cells_magree; [exact HP| exact H|].
  intros a Ha. left. split; lia.
Qed.

Lemma ppres_stk : forall LR SP P m m' lo hi,
  ppres LR SP P m m' -> stk usegs m lo hi -> SP <= lo -> (hi <= P \/ P + 56 <= lo) -> stk usegs m' lo hi.
Proof.
  intros LR SP P m m' lo hi HP ST HS HD. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; split; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma ppres_rw_cells_block : forall LR SP P m m' A cs B k,
  ppres LR SP P m m' -> rw_cells usegs m A cs -> In (B, k) LR -> B <= A -> A + Z.of_nat (cells_size cs) <= B + k ->
  rw_cells usegs m' A cs.
Proof.
  intros LR SP P m m' A cs B k HP H Hin HB HA. eapply rw_cells_magree; [exact HP| exact H|].
  intros a Ha. right; right. exists B, k. split; [exact Hin| lia].
Qed.

Lemma ppres_bytes_at_block : forall LR SP P m m' A bs B k,
  ppres LR SP P m m' -> bytes_at usegs m A bs -> In (B, k) LR -> B <= A -> A + Z.of_nat (length bs) <= B + k ->
  bytes_at usegs m' A bs.
Proof.
  intros LR SP P m m' A bs B k HP H Hin HB HA. eapply bytes_at_magree; [exact HP| exact H|].
  intros a Ha. right; right. exists B, k. split; [exact Hin| lia].
Qed.

Lemma ppres_cj_chain : forall LR SP P m m' T d p B,
  ppres LR SP P m m' -> cj_chain T m d p B -> (forall b, In b B -> In b LR) -> cj_chain T m' d p B.
Proof.
  intros LR SP P m m' T d p B HP H HB. eapply cj_chain_magree; [exact H| exact HP|].
  intros a Ha. right; right. eapply in_cblock_mono; eauto.
Qed.

Lemma ppres_cj_lseg : forall LR SP P m m' T d p q B,
  ppres LR SP P m m' -> cj_lseg T m d p q B -> (forall b, In b B -> In b LR) -> cj_lseg T m' d p q B.
Proof.
  intros LR SP P m m' T d p q B HP H HB. eapply cj_lseg_magree; [exact H| exact HP|].
  intros a Ha. right; right. eapply in_cblock_mono; eauto.
Qed.

Lemma ppres_cj_str : forall LR SP P m m' s B,
  ppres LR SP P m m' -> cj_str m s B -> (forall b, In b B -> In b LR) -> cj_str m' s B.
Proof.
  intros LR SP P m m' s B HP H HB. eapply cj_str_magree; [exact HP| exact H|].
  intros a Ha. right; right. eapply in_cblock_mono; eauto.
Qed.

(* [comment removed for export] *)
Lemma CJST_frame_gen : forall W m m',
  CJST m -> munch W m m' -> wmono usegs m m' ->
  disjoint_from W PHOOKS 24 -> disjoint_from W PGERROR 16 -> disjoint_from W PLCONV 8 -> CJST m'.
Proof.
  intros W m m' (HK & (e1 & e2 & GE) & LC) MU WM D1 D2 D3.
  split; [|split; [exists e1, e2|]]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| assumption]).
Qed.

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
  bytes_at usegs m A bs -> 0 <= j -> (Z.to_nat j + n <= length bs)%nat ->
  bytes_at usegs m (A + j) (firstn n (skipn (Z.to_nat j) bs)).
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
  bytes_at usegs m A bs -> 0 <= i -> (Z.to_nat i < length bs)%nat -> a = wa (A + i) ->
  exists b, nth_error bs (Z.to_nat i) = Some b /\ ov_read_bytes usegs m a 1 = Some [b] /\ at_ bs i = bv_unsigned b.
Proof.
  intros m A bs i a BY Hi Hl ->. destruct (nth_error_lt_some bs (Z.to_nat i) Hl) as [b Hb].
  exists b. split; [exact Hb|]. split; [| unfold at_; rewrite Hb; reflexivity].
  eapply u8ro_read; [exact BY| exact Hb| exact Hi| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma jt_read' : forall m c, mem_inv usegs m -> 34 <= c <= 117 ->
  ov_read_bytes usegs m (Z_to_bv 64 (Z.shiftl (c + -34) 2 + JT)) 4 = Some (le4 (Z_to_bv 64 (jt_off c))).
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
  Variable HI : cj_heap_iface.

  (* [comment removed for export] *)
  Lemma ppres_frame_store : forall SPB LB m0 mo LR SP P lo' hi' m1 m2,
    LHEAP HI SPB LB m0 mo -> (forall b, In b LR -> In b LB) ->
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP ->
    ppres LR SP P m1 m2.
  Proof.
    intros SPB LB m0 mo LR SP P lo' hi' m1 m2 HL HLR MU WM Hlo Hhi a Ha Hp.
    try rewrite alloc_ceiling_eq in Hlo.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hp as [[Hs _]|[[Hd _]|(A' & n' & Hin & Hr)]].
    - lia.
    - unfold PDATA_LO, PIMG_HI in Hd. lia.
    - pose proof (lh_block_range HI _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4 & _). try rewrite alloc_ceiling_eq in R4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ppres_pbuf_store : forall SPB LB m0 mo LR SP P lo' hi' m1 m2,
    LHEAP HI SPB LB m0 mo -> (forall b, In b LR -> In b LB) ->
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> P <= lo' -> hi' <= P + 56 -> alloc_ceiling <= P ->
    ppres LR SP P m1 m2.
  Proof.
    intros SPB LB m0 mo LR SP P lo' hi' m1 m2 HL HLR MU WM Hlo Hhi HP a Ha Hp.
    try rewrite alloc_ceiling_eq in HP.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hp as [[_ Hx]|[[Hd _]|(A' & n' & Hin & Hr)]].
    - lia.
    - unfold PDATA_LO, PIMG_HI in Hd. lia.
    - pose proof (lh_block_range HI _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4 & _). try rewrite alloc_ceiling_eq in R4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ppres_block_store : forall SPB LBX m0 mo A n R LR SP P lo' hi' m1 m2,
    LHEAP HI SPB LBX m0 mo -> Permutation ((A, n) :: R) LBX -> (forall b, In b LR -> In b R) -> alloc_ceiling <= SP ->
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> A <= lo' -> hi' <= A + n ->
    ppres LR SP P m1 m2.
  Proof.
    intros SPB LBX m0 mo A n R LR SP P lo' hi' m1 m2 HL HP HLR HSP MU WM Hlo Hhi a Ha Hc.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & R2 & R3 & R4 & R5).
    try rewrite alloc_ceiling_eq in *. unfold PIMG_LO, PIMG_HI in R5.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hc as [[Hs _]|[[Hd _]|(A' & n' & Hin & Hr)]].
    - lia.
    - unfold PDATA_LO, PIMG_HI in Hd. lia.
    - destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ D]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lheap_frame_store : forall SPB LB m mo lo' hi' m',
    LHEAP HI SPB LB m mo -> munch [(lo', hi')] m m' -> wmono usegs m m' -> alloc_ceiling <= lo' -> hi' <= SPB ->
    LHEAP HI SPB LB m' mo.
  Proof. intros. eapply (lh_frame HI); eauto. constructor; [|constructor]. right; left. cbn. lia. Qed.

  Lemma lheap_block_store : forall SPB LB m mo A n lo' hi' m',
    LHEAP HI SPB LB m mo -> In (A, n) LB -> munch [(lo', hi')] m m' -> wmono usegs m m' -> A <= lo' -> hi' <= A + n ->
    LHEAP HI SPB LB m' mo.
  Proof. intros. eapply (lh_frame HI); eauto. constructor; [|constructor]. do 4 right. exists A, n. cbn. auto. Qed.

  (* [comment removed for export] *)
  Lemma CJST_high_store : forall m m' lo' hi',
    CJST m -> munch [(lo', hi')] m m' -> wmono usegs m m' -> alloc_ceiling <= lo' -> CJST m'.
  Proof.
    intros m m' lo' hi' CJ MU WM Hlo. try rewrite alloc_ceiling_eq in Hlo. eapply CJST_frame; [exact CJ| exact MU| exact WM|].
    intros lo hi Hin. destruct Hin as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia.
  Qed.

  Lemma CJST_block_store : forall SPB LB m0 mo A n m m' lo' hi',
    LHEAP HI SPB LB m0 mo -> In (A, n) LB ->
    CJST m -> munch [(lo', hi')] m m' -> wmono usegs m m' -> A <= lo' -> hi' <= A + n -> CJST m'.
  Proof.
    intros SPB LB m0 mo A n m m' lo' hi' HL Hin CJ MU WM Hlo Hhi.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL Hin) as (R1 & R2 & R3 & R4 & R5). unfold PIMG_LO, PIMG_HI in R5.
    eapply CJST_frame; [exact CJ| exact MU| exact WM|].
    intros lo hi Hin'. destruct Hin' as [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia.
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


End CeilWrap.
End CJ_parse_lemmas.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_utraps.
Module CJ_skipws.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_utraps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition skipws_entry : Z := 0x140f8.

Definition skipws_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (P content length depth : Z) (bs : list byte) (r : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(P + 16, P + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ pbuf_at m' P content length r depth
    /\ bytes_at usegs m' content bs.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (P content len off0 depth : Z) (bs : list byte).
  Hypothesis BY0 : bytes_at usegs m0 content bs.
  Hypothesis LEN : Z.of_nat (length bs) = len.
  Hypothesis PNZ : P <> 0.
  Hypothesis CNZ : 0 < content < 2^64.
  Hypothesis SEP : content + len <= P \/ P + 56 <= content.

  Notation POST := (skipws_post ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                      F fc P content len depth bs (skipws_off bs off0) m0).
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fin (i : Z) : Z :=
    let k := i + Z.of_nat (ws_count (skipn (Z.to_nat i) bs)) in if k =? len then len - 1 else k.

  Lemma fin_off0 : 0 <= off0 < len -> skipws_off bs off0 = fin off0.
  Proof.
    intros H. unfold skipws_off, fin. rewrite LEN.
    destruct (Z.leb_spec 0 off0); [|lia]. destruct (Z.ltb_spec off0 len); [|lia]. reflexivity.
  Qed.

  Lemma fin_stop : forall i b, 0 <= i < len -> nth_error bs (Z.to_nat i) = Some b -> 32 < bv_unsigned b -> fin i = i.
  Proof.
    intros i b Hi Hn Hb. unfold fin.
    replace (ws_count (skipn (Z.to_nat i) bs)) with O.
    2:{ destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E; [reflexivity|]. cbn.
        assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
        rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst.
        destruct (Z.leb_spec (bv_unsigned c) 32); [lia| reflexivity]. }
    cbn [Z.of_nat]. rewrite Z.add_0_r. destruct (Z.eqb_spec i len); lia.
  Qed.

  Lemma fin_ws : forall i b, 0 <= i < len -> nth_error bs (Z.to_nat i) = Some b -> bv_unsigned b <= 32 ->
    fin i = (if i + 1 =? len then len - 1 else fin (i + 1)).
  Proof.
    intros i b Hi Hn Hb. unfold fin.
    destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E.
    { exfalso. assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = None) by (rewrite E; reflexivity).
      rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. discriminate. }
    assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
    rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst c.
    assert (Er : rest = skipn (Z.to_nat (i + 1)) bs).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite <- skipn_skipn with (x := 1%nat) (y := Z.to_nat i).
      hnf. rewrite E. reflexivity. }
    cbn [ws_count]. destruct (Z.leb_spec (bv_unsigned b) 32); [|lia]. rewrite <- Er.
    destruct (Z.eqb_spec (i + 1) len) as [E1|NE1].
    - pose proof (ws_count_le rest) as HL.
      assert (length rest = 0)%nat. { rewrite Er, length_skipn. lia. }
      replace (ws_count rest) with O by lia.
      lazymatch goal with |- (if ?x =? ?y then _ else _) = _ => replace x with y by lia end.
      rewrite Z.eqb_refl. reflexivity.
    - rewrite Nat2Z.inj_succ. replace (i + Z.succ (Z.of_nat (ws_count rest))) with (i + 1 + Z.of_nat (ws_count rest)) by lia.
      reflexivity.
  Qed.

  Lemma cbound : 0 <= content /\ content + len <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ BY0). lia. Qed.

  (* [comment removed for export] *)
  Lemma skipws_loop : forall (k : nat) (i r : Z) (a6 : word) (m : word -> option byte),
    Z.to_nat (len - i) = k -> 0 <= i < len -> r = fin i ->
    rw_cells usegs m P (pbuf_cells content len i depth) ->
    bytes_at usegs m content bs ->
    munch [(P + 16, P + 24)] m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
    evt usegs (skipws_post ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc P content len depth bs r m0)
        (ST 0x14120 m (Z_to_bv 64 content) (Z_to_bv 64 len) (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - content)) (Z_to_bv 64 32) a6).
  Proof.
    induction k as [|k IH]; intros i r a6 m Hk Hi Hr PB BY MU WM MI; [lia|].
    pose proof cbound as CB. pose proof (rw_cells_bound usegs _ _ _ PB) as PBB. rewrite pbuf_cells_size in PBB.
    unfold pbuf_cells in PB.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn. 2:{ apply nth_error_None in Hn. lia. }
    pose proof (u8ro_read usegs m content bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT; [exfalso; lia|]. clear KT.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite (fin_stop i b) in Hr by first [lia | exact Hn]. subst r.
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      zstep. finish.
    - (* [comment removed for export] *)
      rewrite (fin_ws i b) in Hr by first [lia | exact Hn].
      zstep. zstep. zstep.
      if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec (i + 1) len); [exfalso; lia|].
        replace (len - i + -1) with (len - (i + 1)) by lia.
        apply (IH (i + 1) r); try assumption; try lia.
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec (i + 1) len); [| exfalso; lia]. subst r.
        zstep. zstep. zstep. zstep.
        replace (len + -1) with (len - 1) by lia. finish.
  Qed.
End Proofs.

Lemma skipws_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (P content len offset depth : Z) (bs : list byte),
  pbuf_at m P content len offset depth ->
  a0 = wz P -> P <> 0 -> P mod 8 = 0 -> 0 < content < 2^64 ->
  bytes_at usegs m content bs -> Z.of_nat (length bs) = len ->
  0 <= offset <= len ->
  (content + len <= P \/ P + 56 <= content) ->
  mem_inv usegs m ->
  evt usegs (skipws_post ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc P content len depth bs (skipws_off bs offset) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140f8) fc None m (seg_rom usegs)).
Proof.
  intros until bs. intros PB A0 PNZ PAL CNZ BY LEN OFF SEP MI. unfold wz in A0. subst a0.
  pose proof (munch_refl [(P + 16, P + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BY) as CB. pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB.
  pose proof PB as PB'. unfold pbuf_at, pbuf_cells in PB.
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  (* [comment removed for export] *)
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. apply K1. apply align8_land7. exact PAL. }
  zstep. zstep. if_cases K2; zify_cond K2. { exfalso. unfold wz in K2. rewrite unsigned_lit in K2 by lia. lia. }
  zstep. zstep. unfold wz. zstep. if_cases K3; zify_cond K3.
  - (* [comment removed for export] *)
    zstep. rewrite skipws_off_noop by lia. finish.
  - zstep. rewrite zb_lxor_ones by lia. zstep.
    eapply skipws_loop with (i := offset) (k := Z.to_nat (len - offset)); try eassumption; try lia; try reflexivity.
    apply fin_off0; [exact LEN| lia].
Qed.
End CJ_skipws.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
Import CJ_pbuf.
Import CJ_parse_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section T.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (c0 c1 c2 c3 : byte).
  Hypothesis RO : ro_cells usegs m A [C1 c0; C1 c1; C1 c2; C1 c3].
  Hypothesis MI : mem_inv usegs m.

  (* [comment removed for export] *)
  Notation ST pc x5 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)) (only parsing).
  Notation POST := (hex4_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A [c0;c1;c2;c3] m) (only parsing).
  Notation K0 := (bv_unsigned c0) (only parsing).
  Notation K1 := (bv_unsigned c1) (only parsing).
  Notation K2 := (bv_unsigned c2) (only parsing).
  Notation K3 := (bv_unsigned c3) (only parsing).
  Notation L z := (Z_to_bv 64 z) (only parsing).

  Lemma AB : 0 <= A /\ A + 4 <= 2^64.
  Proof. pose proof (ro_cells_bound usegs _ _ _ RO) as B. cbn [cells_size csize Nat.add] in B. lia. Qed.
  Lemma R0 : 0 <= K0 < 256. Proof. pose proof (bv_unsigned_in_range 8 c0) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma R1 : 0 <= K1 < 256. Proof. pose proof (bv_unsigned_in_range 8 c1) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma R2 : 0 <= K2 < 256. Proof. pose proof (bv_unsigned_in_range 8 c2) as R. change (bv_modulus 8) with 256 in R. lia. Qed.
  Lemma R3 : 0 <= K3 < 256. Proof. pose proof (bv_unsigned_in_range 8 c3) as R. change (bv_modulus 8) with 256 in R. lia. Qed.

  Ltac pre := intros; pose proof AB; pose proof R0; pose proof R1; pose proof R2; pose proof R3;
              pose proof (munch_refl [] m) as MU; pose proof (wmono_refl usegs m) as WM.
  Ltac ml := Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Lemma L_fail : forall x5 x10 x11 x12 x13 x14 x15 x16 x17,
    evt usegs POST (ST 0x1555c x5 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof. pre. zstep. zstep. finish; [exact (proj2 RO) | lia | lia]. Qed.

  (* [comment removed for export] *)
  Lemma L_comb : forall (J0 J1 J2 J3 : Z) x5,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 -> 0 <= K3 + J3 <= 15 ->
    evt usegs POST (ST 0x15530 x5 (L K3) (L K0) (L J0) (L K1) (L J1) (L K2) (L J2) (L J3)).
  Proof.
    pre. do 11 zstep. finish.
    - exact (proj2 RO).
    - rewrite ?zb_shiftl_mul by lia. ml.
    - rewrite ?zb_shiftl_mul by lia. ml.
  Qed.

  Ltac kill K := first [exfalso; clear -K; match goal with H : _ |- _ => idtac end; lia | exfalso; lia].

  (* [comment removed for export] *)
  Lemma L_b3 : forall (J0 J1 J2 : Z) x5 x17,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 -> 0 <= K2 + J2 <= 15 ->
    evt usegs POST (ST 0x154bc x5 (L A) (L K0) (L J0) (L K1) (L J1) (L K2) (L J2) x17).
  Proof.
    pre. do 4 zstep. if_cases Ka; zify_cond Ka.
    - (* [comment removed for export] *) do 3 zstep. if_cases Kb; zify_cond Kb.
      + (* [comment removed for export] *) do 3 zstep. if_cases Kc; zify_cond Kc; [apply L_fail|]. zstep. apply L_comb; ml.
      + zstep. zstep. apply L_comb; ml.
    - zstep. zstep. apply L_comb; ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_b2 : forall (J0 J1 : Z) x5 x15 x16 x17,
    0 <= K0 + J0 <= 15 -> 0 <= K1 + J1 <= 15 ->
    evt usegs POST (ST 0x154a0 x5 (L A) (L K0) (L J0) (L K1) (L J1) x15 x16 x17).
  Proof.
    pre. do 4 zstep. if_cases Ka; zify_cond Ka.
    - do 3 zstep. if_cases Kb; zify_cond Kb.
      + do 3 zstep. if_cases Kc; zify_cond Kc; [apply L_fail|]. do 3 zstep. if_cases Kg; zify_cond Kg; [apply L_b3; ml| exfalso; ml].
      + do 3 zstep. if_cases Kg; zify_cond Kg; [apply L_b3; ml| exfalso; ml].
    - do 3 zstep. if_cases Kg; zify_cond Kg; [exfalso; ml|]. apply L_b3; ml.
  Qed.

  (* [comment removed for export] *)
  Lemma L_b1 : forall (J0 : Z) x5 x13 x14 x15 x16 x17,
    0 <= K0 + J0 <= 15 ->
    evt usegs POST (ST 0x1544c x5 (L A) (L K0) (L J0) x13 x14 x15 x16 x17).
  Proof.
    pre. do 4 zstep. if_cases Ka; zify_cond Ka.
    - do 3 zstep. if_cases Kb; zify_cond Kb.
      + do 3 zstep. if_cases Kc; zify_cond Kc; [apply L_fail|]. do 3 zstep. if_cases Kg; zify_cond Kg; [exfalso; ml|]. apply L_b2; ml.
      + do 3 zstep. if_cases Kg; zify_cond Kg; [apply L_b2; ml| exfalso; ml].
    - do 3 zstep. if_cases Kg; zify_cond Kg; [apply L_b2; ml| exfalso; ml].
  Qed.

  (* [comment removed for export] *)
  Lemma L_entry : forall x5 x11 x12 x13 x14 x15 x16 x17,
    evt usegs POST (ST 0x153f8 x5 (L A) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    pre. do 4 zstep. if_cases Ka; zify_cond Ka.
    - do 3 zstep. if_cases Kb; zify_cond Kb.
      + do 3 zstep. if_cases Kc; zify_cond Kc; [apply L_fail|]. do 3 zstep. if_cases Kg; zify_cond Kg; [exfalso; ml|]. apply L_b1; ml.
      + do 3 zstep. if_cases Kg; zify_cond Kg; [apply L_b1; ml| exfalso; ml].
    - do 3 zstep. if_cases Kg; zify_cond Kg; [apply L_b1; ml| exfalso; ml].
  Qed.
End T.

Lemma hex4_spec : hex4_stmt.
Proof.
  unfold hex4_stmt. intros until b4. intros BY LEN MI A0. unfold PARSE_HEX4. subst a0.
  destruct b4 as [|c0 [|c1 [|c2 [|c3 [|]]]]]; cbn in LEN; try discriminate.
  apply L_entry; [| exact MI]. split; [cbn; repeat split; exact I| cbn; rewrite ?app_nil_r; exact BY].
Qed.
