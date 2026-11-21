(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayLP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayBlock.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition sym_ok (s : osym) : Prop :=
  match s with OLit c => 0 <= c < 256 | OPair lc dc => 257 <= lc <= 285 /\ 0 <= dc <= 29 end.

Section Facts.
Variable b : oblock.

(* [comment removed for export] *)
Definition usedLb (c : Z) : bool := 0 <? fL b c.
Definition usedDb (d : Z) : bool := (0 <? gD b d) || forcedD b d.
(* [comment removed for export] *)
Definition BC' : Z -> Z := ffreq (ob_BC b) (ob_bforced b).

Record oblock_ok (lbs : Z) : Prop := {
  ok_syms : Forall sym_ok (ob_syms b);
  ok_N : 1 <= NSYM b <= lbs - 1;
  ok_lbs : 128 <= lbs;
  (* [comment removed for export] *)
  ok_TL : exists zL, tree_facts zL 286 15 (fL b) [] /\ zt_kraft zL /\ (forall c, 0 <= c < 286 -> ob_lenL b c = zt_len zL c);
  (* [comment removed for export] *)
  ok_TD : exists zD, tree_facts zD 30 15 (gD b) (ob_forced b) /\ zt_kraft zD /\ (forall d, 0 <= d < 30 -> ob_lenD b d = zt_len zD d);
  (* [comment removed for export] *)
  ok_TB : exists zB, tree_facts zB 19 7 (ob_BC b) (ob_bforced b) /\ zt_kraft zB /\ (forall x, 0 <= x < 19 -> ob_BD b x = zt_len zB x);
  (* [comment removed for export] *)
  ok_WB : zsum (ob_BC b) 0 19 <= 316;
  (* [comment removed for export] *)
  ok_blc : 3 <= ob_blcodes b <= 19 /\ (ob_BD b 15 = 0 -> ob_blcodes b <= 18);
  (* [comment removed for export] *)
  ok_Hc1 : ob_Hc1 b = 14 + 3 * ob_blcodes b + zsum (fun x => ob_BC b x * (ob_BD b x + xb_of_bl x)) 0 19;
  (* [comment removed for export] *)
  ok_sc1 : forall j, 1 <= j <= 15 -> ob_BC b j <= countZ (fun c => usedLb c && (ob_lenL b c =? j)) (zrange 0 286)
                                               + countZ (fun d => usedDb d && (ob_lenD b d =? j)) (zrange 0 30);
  ok_sc2 : zsum (ob_BC b) 1 15 + 3 * ob_BC b 16 <= vU b + vV b;
  ok_sc3 : 4 * ob_BC b 16 <= vU b + vV b;
  ok_sc4a : ob_BC b 0 = vR1 b 1 + vR1 b 2 + vR1 b 3 + 2 * (vR2 b 1 + vR2 b 2 + vR2 b 3);
  ok_sc4b : ob_BC b 17 = vRA b 1 + vRA b 2 + vRA b 3;
  ok_sc4c : ob_BC b 18 = vRB b 1 + vRB b 2 + vRB b 3 + vRLONG b;
  (* [comment removed for export] *)
  ok_dyn : ob_Hc1 b + ssum (dcostS b) (ob_syms b) + ob_lenL b 256 <= ssum scostS (ob_syms b) + 6
}.
End Facts.
