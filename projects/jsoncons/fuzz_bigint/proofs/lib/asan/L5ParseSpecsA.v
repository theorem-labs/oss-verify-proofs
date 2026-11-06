(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface
     BigModel BigFactsRun BigFactsDigits L5Defs L5Core L5DefsA L5CoreA L5CoreSpecsA L5StepA L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5PSA.
Import L5A. Import L5CA. Import L5CSA. Import L5CB.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition digits_ok (ds : list Z) : Prop := Forall (fun c => 48 <= c <= 57) ds.
Definition split_sign (s : list Z) : bool * list Z :=
  match s with c :: t => if Z.eqb c 45 then (true, t) else (false, s) | [] => (false, []) end.
Definition parses (s : list Z) : Prop := (1 <= length (snd (split_sign s)))%nat /\ digits_ok (snd (split_sign s)).
Definition no_parse (s : list Z) : Prop := length (snd (split_sign s)) = 0%nat \/ ~ digits_ok (snd (split_sign s)).

(* [comment removed for export] *)
Definition vblk (m : nat) : Z := if (m <? 39)%nat then 64 else 8 * round_up (Z.of_nat (num_words_est m)).
Definition parse_credit (L : asan_layout) (cr : credit) (m : nat) : Prop :=
  acredit_ok L cr (vblk m) /\ acredit_ok L (adebit L cr (vblk m)) (vblk m).
Definition parse_debit (L : asan_layout) (cr : credit) (m : nat) : credit := adebit L (adebit L cr (vblk m)) (vblk m).

(* [comment removed for export] *)
Definition res_fb (fb : Z) (n : nat) (neg : bool) : Z :=
  fb + (if (3 <=? n)%nat then 1 else 0) + (if (neg && (1 <=? n)%nat)%bool then 2 else 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DETAIL : Z := 0x8e9fc.
Definition DETAIL_SCR : Z := 176 + ADDD_SCR.    (* [comment removed for export] *)

Definition parse_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (o sp fb : Z) (neg : bool) (ds : list Z) (SCR : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let V := dec ds in let n := nwords V in
  exists st',
    L5.big_at RSEGS M' o (L5.BO (res_fb fb n neg) n st') /\ L5C.obj_limbs RSEGS M' (L5.BO (res_fb fb n neg) n st') (wlist V n)
    /\ match st' with
       | L5.BInl _ _ => (n <= 2)%nat /\ LB' = LB
       | L5.BDyn cap q => (3 <= n)%nat /\ cap = round_up (Z.of_nat n) /\ LB' = (q, 8 * cap) :: LB /\ afresh L ar LB (FF ++ LKq) M' q (8 * cap)
       end
    /\ credit_le (parse_debit L cr (length ds)) cr'
    /\ ahpres L ar LB FF sp SCR [(o, 32)] M M'.

Definition noparse_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte)
           (o sp fb : Z) (m : nat) (SCR : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  LB' = LB /\ L5.big_at RSEGS M' o (L5.BO fb 0 (L5.BInl 0 0))
  /\ credit_le (parse_debit L cr m) cr'
  /\ ahpres L ar LB FF sp SCR [] M M'.

Definition detail_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fb : Z) (neg : bool) (ds : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  ( ((1 <= length ds)%nat /\ digits_ok ds /\ getr R' 11%bv = Z_to_bv 64 0 /\ parse_post L ar LB FF LKq cr M M' o sp fb neg ds DETAIL_SCR LB' cr')
  \/ ((length ds = 0%nat \/ ~ digits_ok ds) /\ getr R' 11%bv = Z_to_bv 64 22 /\ noparse_post L ar LB FF cr M M' o sp fb (length ds) DETAIL_SCR LB' cr') ).

(* [comment removed for export] *)
Definition parser_spec_at (pc SCR cls : Z) (oreg : bv 5) (with_neg : bool)
           (POST : asan_layout -> asan_run -> list (Z * Z) -> list fframe -> list fframe -> credit -> (word -> option byte) -> (word -> option byte) ->
                   bvmap 5 word -> bvmap 5 word -> Z -> Z -> Z -> bool -> list Z -> list (Z * Z) -> credit -> Prop)
           (CRED : list Z -> nat)
           (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (p o sp r fb : Z) (neg : bool) (s : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (Z.of_nat (length s)) ->
    (with_neg = true -> getr R 12%bv = Z_to_bv 64 (if neg then 1 else 0)) -> getr R oreg = Z_to_bv 64 o ->
    (length s <= 4999)%nat -> parse_credit L cr (CRED s) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = cls -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCR ->
    ffr FF LK 5 -> ffrk 2 FF LK 2 -> ffrs FF sp ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> Z.land fb 3 = 0 -> aobj FF o 32 -> shadow_zero M o 4 ->
    (* [comment removed for export] *)
    L5.bytes_at RSEGS M p s -> Forall (fun c => 0 <= c < 256) s -> asrc IL LB FF M p (Z.of_nat (length s)) ->
    (p + Z.of_nat (length s) <= o \/ o + 32 <= p) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        POST L ar LB FF LK' cr M M' R R' o sp fb neg s LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.

Definition detail_spec := parser_spec_at DETAIL DETAIL_SCR 16 13%bv true detail_post (fun s => length s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TOBIG3 : Z := 0x9177c.
Definition TOBIG4 : Z := 0x8e980.
Definition TOBIG_SCR : Z := 16 + DETAIL_SCR.

Definition tobig_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fb : Z) (_ : bool) (s : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let neg := fst (split_sign s) in let ds := snd (split_sign s) in
  regs_preserved R R' /\
  ( (parses s /\ getr R' 11%bv = Z_to_bv 64 0 /\ parse_post L ar LB FF LKq cr M M' o sp fb neg ds TOBIG_SCR LB' cr')
  \/ (no_parse s /\ getr R' 11%bv = Z_to_bv 64 22 /\ noparse_post L ar LB FF cr M M' o sp fb (length ds) TOBIG_SCR LB' cr') ).

Definition tobig_spec_at (pc : Z) := parser_spec_at pc TOBIG_SCR 0 12%bv false tobig_post (fun s => length (snd (split_sign s))).
Definition tobig3_spec := tobig_spec_at TOBIG3.
Definition tobig4_spec := tobig_spec_at TOBIG4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSTR : Z := 0x8e628.
Definition CSTR_SCR : Z := 32 + Z.max TOBIG_SCR 2560.
Definition ALIT : Z := 0x22960.
Definition A0 : Z := 0x16af9c0daf145395.
Definition A1 : Z := 0x2a9f3636273caaf2.
Definition alit_digits : list Z := [53;54;54;53;52;50;53;48;53;54;52;48;53;54;49;51;53;52;49;53;54;51;49;53;53;52;53;51;49;53;53;52;53;49;51;56;49;51].

Definition cstr_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fbo : Z) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  L5.big_at RSEGS M' o (L5.BO (Z.land fbo 252) 2 (L5.BInl A0 A1)) /\
  credit_le (parse_debit L cr 38) cr' /\
  ahpres L ar LB FF sp CSTR_SCR [(o, 32)] M M'.

Definition cstr_spec (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r fbo : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ALIT -> parse_credit L cr 38 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp CSTR_SCR ->
    ffr FF LK 5 -> ffrk 2 FF LK 2 -> ffrs FF sp ->
    L5.img_clear M 0x10000 0x3c000 ->                               (* [comment removed for export] *)
    (* [comment removed for export] *)
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        cstr_post L ar LB FF cr M M' R R' o sp fbo cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R CSTR M model) K.

End SCFG_1.
End L5PSA.
