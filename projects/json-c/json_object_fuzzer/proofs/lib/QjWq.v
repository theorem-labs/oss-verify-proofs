(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKJh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxCw.Mq0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Hooked.
Context {ptr : Type}.
Variable peq : ptr -> ptr -> bool.
Hypothesis peq_spec : forall p q, peq p q = true <-> p = q.
Variable MH : owned ptr -> Z -> Prop.

Fixpoint asafeh {A} (X : owned ptr) (t : aprog ptr A) (Q : A -> owned ptr -> Prop) : Prop :=
match t with
| ARet a => Q a X
| AUnr => False
| AMalloc n k =>
0 <= n /\ MH X n
/\ (forall p, ~ In p (map fst X) -> n < 2^63 -> asafeh ((p, n) :: X) (k (Some p)) Q)
/\ asafeh X (k None) Q
| AFree p k => In p (map fst X) /\ asafeh (xremove peq p X) k Q
end.

Section AMSpecH.
Context {St : Type}.

Definition aspech {A} (P : aassn ptr St) (m : AM ptr St A) (Q : A -> aassn ptr St) : Prop :=
forall X s, P X s -> asafeh X (m s) (fun r X' => Q (fst r) X' (snd r)).

End AMSpecH.
End Hooked.

Arguments asafeh {ptr} peq MH {A} X t Q.
Arguments aspech {ptr} peq MH {St A} P m Q.

Definition zcount_eq (n : Z) (zs : list Z) : Z := Z.of_nat (length (filter (Z.eqb n) zs)).

Definition arr_sizes_ok (L : Z) (arr : list Z) : Prop :=
arr = [] \/ arr = [L * 4] \/ arr = [L * 4; L * 4] \/ arr = [L * 1; L * 4; L * 4].

Definition RUNS_CAP (L : Z) : Z := 2 * L + 8.
Definition PNODES_CAP (L : Z) : Z := L + 1.
Definition ROWS_CAP : Z := 109.

Definition sizes_ok (L : Z) (zs : list Z) : Prop :=
exists dyn arr, zs = dyn ++ arr
/\ Forall (fun n => n = RUN_SIZEOF \/ n = PNODE_SIZEOF \/ n = ROW_SIZEOF) dyn
/\ zcount_eq RUN_SIZEOF dyn <= RUNS_CAP L
/\ zcount_eq PNODE_SIZEOF dyn <= PNODES_CAP L
/\ zcount_eq ROW_SIZEOF dyn <= ROWS_CAP
/\ arr_sizes_ok L arr.

Definition MHcaps {ptr : Type} (L : Z) (X0 : owned ptr) : owned ptr -> Z -> Prop :=
fun X n => exists ours, X = ours ++ X0 /\ sizes_ok L (n :: map snd ours).

Definition ALL_TYPES : list Z :=
[TY_LTR; TY_RTL; TY_AL; TY_EN; TY_AN; TY_ES; TY_ET; TY_CS; TY_NSM; TY_BN; TY_BS; TY_SS; TY_WS; TY_ON;
TY_LRE; TY_RLE; TY_LRO; TY_RLO; TY_PDF; TY_LRI; TY_RLI; TY_FSI; TY_PDI].

Record tables_ok (T : ftables) : Prop := mkTOK {
tok_bididx   : forall i, 0 <= i < BIDIDX_LEN -> 0 <= t_bididx T i /\ t_bididx T i + 255 < BIDDAT_LEN;
tok_biddat   : forall i, 0 <= i < BIDDAT_LEN -> 0 <= t_biddat T i < LIN2TYPE_LEN;
tok_lin2type : forall i, 0 <= i < LIN2TYPE_LEN -> 0 <= t_lin2type T i <= 4294967295 /\ t_lin2type T i <> TY_SENTINEL;
tok_lin2type_valid : forall i, 0 <= i < LIN2TYPE_LEN -> In (t_lin2type T i) ALL_TYPES;
tok_brtidx   : forall i, 0 <= i < BRTIDX_LEN -> 0 <= t_brtidx T i /\ t_brtidx T i + 127 < BRTDAT_LEN;
tok_brkidx   : forall i, 0 <= i < BRKIDX_LEN -> 0 <= t_brkidx T i /\ t_brkidx T i + 63 < BRKDAT_LEN
}.

Definition FUEL (L : Z) : nat := Z.to_nat (L + 128).

Definition fuzz_one_aspech_stmt : Prop :=
forall (ptr : Type) (peq : ptr -> ptr -> bool) (peq_spec : forall p q, peq p q = true <-> p = q)
(TAB : ftables) (TABOK : tables_ok TAB)
(data : list Z) (Hdata : Forall (fun b => 0 <= b < 256) data) (Hlen : zlength data < 2^26)
(fuel : nat) (Hfuel : (FUEL (zlength data / 4) <= fuel)%nat)
(X0 : owned ptr),
asafeh peq (MHcaps (zlength data / 4) X0) X0 (fuzz_one TAB fuel data)
(fun r X' => r = 0 /\ exists leak, X' = leak ++ X0 /\ arr_sizes_ok (zlength data / 4) (map snd leak)).

