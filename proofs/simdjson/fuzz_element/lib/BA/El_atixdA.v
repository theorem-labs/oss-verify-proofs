From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA El_callsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac spcX := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
  lazymatch pc with
  | Z_to_bv _ 0xb3a20 => idtac "AT LOOPHEAD"
  | Z_to_bv _ 0xb3a8c => idtac "AT FOUND"
  | Z_to_bv _ 0xb39c0 => idtac "AT NOTFOUND"
  | Z_to_bv _ 0xb396c => idtac "AT NOTARR"
  | Z_to_bv _ 0x81794 => idtac "AT MEMSET"
  | _ => idtac "AT OTHER"
  end | _ => idtac "NOTEVT" end.
Ltac tgoX t p := lazymatch p with
  | nil => t
  | cons false ?p' => lazymatch t with TNode ?l _ _ => tgoX l p' end
  | cons true ?p' => lazymatch t with TNode _ _ ?r => tgoX r p' end end.
Ltac regX p := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
  let t := tgoX R p in lazymatch t with TNode _ ?v _ => idtac v end end.
Ltac regsX := spcX; idtac "ra"; regX [false]; idtac "sp"; regX [true]; idtac "s0"; regX [true; false; false];
  idtac "s1"; regX [false; true; false]; idtac "a0"; regX [true; true; false]; idtac "a1"; regX [false; false; true];
  idtac "a2"; regX [true; false; true]; idtac "a3"; regX [false; true; true].
Ltac regsLX := idtac "a4"; regX [true; true; true]; idtac "a5"; regX [false; false; false; false];
  idtac "a6"; regX [true; false; false; false]; idtac "a7"; regX [false; true; false; false]; idtac "t0"; regX [false; true];
  idtac "t1"; regX [true; true]; idtac "t2"; regX [false; false; false]; idtac "t3"; regX [true; false; true; true].
Ltac pcX := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.
Ltac outcX := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  first [ match goal with H : rw_cells asegs mc ?a [_; _; _; _] |- _ => idtac "CUR4" a; let T := type of H in idtac T end | idtac "NOCUR4" ];
  first [ match goal with H : rw_cells asegs mc ?a [_; _; _] |- _ => idtac "CUR3" a; let T := type of H in idtac T end | idtac "NOCUR3" ];
  first [ match goal with H : stk asegs mc _ ?h |- _ => idtac "STKCUR" h end | idtac "NOSTKCUR" ] end.
Ltac notmsX := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv _ ?z) _ _ _ _) => assert_fails (assert (z = e_asan_memset) by (vm_compute; reflexivity))
  | _ => idtac end.
Ltac normX := repeat (rewrite land32_tnext by lia); rewrite ?mod32_tnext;
  repeat match goal with H : tnext ?w = _ |- context [tnext ?w] => rewrite H end;
  repeat match goal with H : ttype ?w = ?c |- context [ttype ?w] => is_Zlit c; rewrite H end.
Ltac stX := zstep; fix_lit_store; normX; anorm; normX.
Ltac ifkX := first [ if_false | if_true
  | (let K := fresh "Kc" in if_cases K; zify_cond K; rewrite ?land64_mod, ?a_signed_small in K by lia; [exfalso; lia | clear K])
  | (let K := fresh "Kc" in if_cases K; zify_cond K; rewrite ?land64_mod, ?a_signed_small in K by lia; [clear K | exfalso; lia]) ].
Ltac runX := repeat (notmsX; first [ stX | ifkX ]).

Lemma le8_nth7X : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma u64s_read7X : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.
Lemma tape_read_typeX : forall m TAPE (tws : list Z) (i : Z),
  bytes_at asegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes asegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read asegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7X by (rewrite length_map; lia).
  rewrite <- le8_nth7X by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Definition atix_W (q out : Z) : list (Z * Z) := [(q + -32, q); (out, out + 24)].
Definition atix_frame (ra s0 s1 : word) (j0 : list byte) : list cell := [CB 8 j0; C8 s1; C8 s0; C8 ra].
