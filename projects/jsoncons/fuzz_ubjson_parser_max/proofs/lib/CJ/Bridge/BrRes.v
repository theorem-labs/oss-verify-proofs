(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Bridge_BrRes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRes.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."], [["1list"; "1prod"; "2eq"; "3Z"; "4POT0"; "4pot"; "5minit"; "5strip"; "0resv"; "0secret"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition EVM : nat := 8%nat.
Definition EVF : nat := 80%nat.
Definition AMC : Z := 65.
Definition GMAX : Z := 2^20 + 4096.
Definition am_pot (cs : mstate) : Z :=
c_avail_meta_count (s_ctx cs) + NSLOTS * c_avail_meta_area_count (s_ctx cs).
Definition pot (cs : mstate) : Z := NSLOTS * 2 ^ (c_meta_alloc_shift (s_ctx cs)) - am_pot cs.
Definition POT0 : Z := NSLOTS.
Lemma pot_init : ltac2:(TCodec.tc2 tcn__CJ_Bridge_BrRes "B'3'0'1%1233%311'2&5&7&6r2r1%3221%511%711&4%:3?21pB<1pDA1").
Proof. intros. reflexivity. Qed.
Definition is_fixed (flags : Z) : bool := negb (Z.land flags MAP_FIXED =? 0).
Definition ecost (e : ev) : Z :=
match e with
| EBrk req => if req =? 0 then 0 else 2 * PGSZ
| EMmap _ len _ flags => if is_fixed flags then 0 else mmap_len len
| _ => 0
end.
Definition elen_ok (n PA : Z) (e : ev) : Prop :=
match e with
| EMmap _ len prot flags =>
is_fixed flags = true
\/ (prot = PROT_NONE /\ NSLOTS * len <= 2 * PGSZ * PA)
\/ (prot <> PROT_NONE /\ mmap_len len <= Z.max GMAX (round_up_pg (n + IB + UNIT)))
| _ => True
end.
Definition efree_ok (e : ev) : Prop :=
match e with EMunmap _ _ => True | _ => False end.
Definition good (e : ev) (z : Z) : Prop :=
match e with
| EMmap _ _ _ flags => is_fixed flags = true \/ is_err z = false
| EMprotect _ _ _ => z = 0
| EMunmap _ _ => z = 0
| _ => True
end.
Fixpoint gtree {R} (E : ev -> Prop) (ne : nat) (bb : Z) (t : M R) (Q : R -> Prop) {struct t} : Prop :=
match t with
| SRet r => Q r
| SVis (EUndef _) _ => True
| SVis e k =>
match ne with
| O => False
| S ne' => E e /\ ecost e <= bb /\ forall z, good e z -> gtree E ne' (bb - ecost e) (k z) Q
end
end.
Lemma gtree_vis_inv {R} : forall E ne bb e (k : Z -> M R) Q,
gtree E ne bb (SVis e k) Q -> match e with EUndef _ => False | _ => True end ->
exists ne', ne = S ne' /\ E e /\ ecost e <= bb /\ forall z, good e z -> gtree E ne' (bb - ecost e) (k z) Q.
Proof.
intros E ne bb e k Q H He. destruct e; try (destruct He; fail); cbn [gtree] in H;
(destruct ne as [|ne']; [destruct H|]); exists ne'; destruct H as (H1 & H2 & H3); auto.
Qed.
Lemma gtree_mono {R} : forall (E E' : ev -> Prop) (Q Q' : R -> Prop),
(forall e, E e -> E' e) -> (forall r, Q r -> Q' r) ->
forall t ne ne' bb bb', (ne <= ne')%nat -> bb <= bb' -> gtree E ne bb t Q -> gtree E' ne' bb' t Q'.
Proof.
intros E E' Q Q' HE HQ t. induction t as [r|e k IH]; intros ne ne' bb bb' Hne Hbb H; cbn [gtree] in *.
- auto.
- destruct e; try exact I;
(destruct ne as [|ne0]; [destruct H|]); (destruct ne' as [|ne0']; [lia|]);
destruct H as (H1 & H2 & H3); (split; [auto|]); (split; [lia|]);
intros z Hz; (eapply IH; [| |apply H3; exact Hz]); lia.
Qed.
Definition CALLB (n PA : Z) : Z :=
Z.max GMAX (round_up_pg (n + IB + UNIT)) + Z.max 0 ((2 * PGSZ * PA) / NSLOTS) + 2 * PGSZ.
Record model_bounds : Prop := MB {
mb_malloc : forall cs L n, creach cs L -> 0 <= n -> size_overflows n = false ->
gtree (elen_ok n (pot cs + AMC)) EVM (CALLB n (pot cs + AMC)) (cmalloc cs n)
(fun r => snd r <> None /\ pot (fst r) <= pot cs + AMC);
mb_free : forall cs L c, creach cs L -> In c (ld_live L) ->
gtree efree_ok EVF 0 (cfree cs (Some c)) (fun cs' => pot cs' <= pot cs)
}.
End CEIL_WRAP_1.
