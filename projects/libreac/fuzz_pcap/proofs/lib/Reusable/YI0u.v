(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0u.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP09 YI04 YI09 YI0t YI0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Export YI00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b.
Variable segs : list Segment.
Lemma arr16_app1 : forall mem mem' base l v,
arr16 segs mem base l -> val_mem segs mem' (base + 2 * Z.of_nat (length l)) 2 v -> 0 <= v < 65536 ->
(forall a, base <= a < base + 2 * Z.of_nat (length l) -> mbyte segs mem' a = mbyte segs mem a) ->
arr16 segs mem' base (l ++ [v]).
Proof.
intros mem mem' base l v H Hv Hr Hfr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. destruct (H j Hlt) as [Hv0 Hr0]. split; [|exact Hr0].
intros k Hk. rewrite Hfr; [apply Hv0; exact Hk|]. cbn in Hk. lia.
- assert (j = length l) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. split; [exact Hv | exact Hr].
Qed.
End b.
Record lzw_v := mkLV { v_LC : list Z; v_LD : list Z }.
Definition child_abs (idl : Z) (X : lzw_abs) (LC : list Z) (q c : Z) : Z :=
let vLI := nth (Z.to_nat q) (la_LI X) 0 in
let vLM := nth (Z.to_nat q) (la_LM X) 0 in
if negb (vLI =? 0) && (nth (Z.to_nat q) LC 0 =? c) then vLI
else if vLM =? 0 then 0 else nth (Z.to_nat ((vLM - 1) * idl + c)) (la_TM X) 0.
Definition init_child (idl : Z) (X : lzw_abs) (c1 c2 : Z) : Z := nth (Z.to_nat (c1 * idl + c2)) (la_TI X) 0.
Definition px (PIX : list Z) (i : Z) : Z := nth (Z.to_nat i) PIX 0.
Definition vx_map (idl : Z) (X : lzw_abs) (m c s1 : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in mkLA TI LM LI (updn TM (Z.to_nat ((m - 1) * idl + c)) dp) s1 (lp + 1) (dp + 1) mp (Cn + 1) R.
Definition vx_first (X : lzw_abs) (q s1 : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in mkLA TI LM (updn LI (Z.to_nat q) dp) TM s1 (lp + 1) (dp + 1) mp (Cn + 1) R.
Definition vx_switch (idl : Z) (X : lzw_abs) (q c s1 : Z) : lzw_abs :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
mkLA TI (updn LM (Z.to_nat q) mp) LI (updn (zero_range TM (Z.to_nat ((mp - 1) * idl)) (Z.to_nat idl)) (Z.to_nat ((mp - 1) * idl + c)) dp) s1 (lp + 1) (dp + 1) (mp + 1) (Cn + 1) R.
