(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RF_get_meta.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => let v := eval vm_compute in (bv_unsigned pc) in idtac "PC" v | _ => idtac "no evt goal" end.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition rrealloc_hdr_post (sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (s2v : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29,
    ms' = MS (mkR (Z_to_bv 64 0x2b52f4) sp gp tp x5 x6 x7 a1 a0 a1 x11 x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 s2v) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
             F (Z_to_bv 64 0x2b3d38) fc None m (seg_rom ctusegs).

Lemma zx32_wz' x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rrealloc_t4 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (s2v : Z),
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 s2v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 s2v) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b52e4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros. st1. st1. st1. st1. apply evt_done. unfold rrealloc_hdr_post. do 12 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t3a : forall ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (s2v n sc : Z),
  bv_unsigned a1 = n -> 0 <= n < 2^32 -> 0 <= sc < 64 -> (n < 131052 \/ sc < 48) ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 s2v F fc m)
      (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 0x20000) s0 s1 a0 a1 a2 (wz sc) a4 a5 a6 a7 (Z_to_bv 64 s2v) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b51e0) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros HN NR SC NOM.
  st1. st1. if_cases K1; zify_cond K1.
  - apply rrealloc_t4.
  - st1. st1. if_cases K2; zify_cond K2.
    + apply rrealloc_t4.
    + exfalso. rewrite wz_unsigned in K2 by lia. rewrite HN in K1. lia.
Qed.


(* [comment removed for export] *)
Lemma rrealloc_t3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (s2v n sc av : Z),
  bv_unsigned a1 = n -> 0 <= n < 2^32 -> 0 <= sc < 64 -> (n < 131052 \/ sc < 48) -> 0 <= av < 2^63 -> av < n ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 s2v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz sc) a4 a5 a6 (Z_to_bv 64 av) (Z_to_bv 64 s2v) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b5140) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until av. intros HN NR SC NOM AV MOVE.
  st1. st1. st1. if_cases K1; zify_cond K1.
  - apply (rrealloc_t3a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s2v n sc HN NR SC NOM).
  - st1. if_cases K2; zify_cond K2.
    + apply (rrealloc_t3a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s2v n sc HN NR SC NOM).
    + exfalso. rewrite ?unsigned_lit in K2 by lia. rewrite ?HN in K2. lia.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t2b : forall ra sp gp tp t1 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (P E rsv n sc : Z),
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> P <= E -> E + 1 <= 2^63 -> 0 <= rsv <= E - P -> rsv < 2^32 ->
  bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  0 <= n < 2^32 -> 0 <= sc < 64 -> (n < 131052 \/ sc < 48) -> E - P < n ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (E - rsv) F fc m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) t1 (wz rsv) s0 s1 a0 a1 a2 (wz sc) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b5118) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros HP HN P0 ELO EHI RSV RSV32 RB0r RE0 NR SC NOM MOVE.
  pose proof (bytes_at_read ctusegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read ctusegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  (* [comment removed for export] *)
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  (* [comment removed for export] *)
  change (Z_to_bv 64 E) with (wa E).
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
  rewrite HP. replace (E + - P) with (E - P) by lia.
  apply (rrealloc_t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (E - rsv) n sc (E - P) HN NR SC NOM ltac:(lia) MOVE).
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t2 : forall ra sp gp tp t1 t2 s0 s1 a0 a1 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (P B E stride idx b3 r32 n sc : Z),
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> 0 <= B -> 16 <= stride -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  E = B + 16 + stride * idx + stride - 4 -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  0 <= n < 2^32 -> 0 <= sc < 64 -> (n < 131052 \/ sc < 48) -> E - P < n ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (E - rsv) F fc m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) t1 t2 s0 s1 a0 a1 (wz B) (wz sc) a4 a5 (Z_to_bv 64 stride) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b50d0) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros rsv0 rsv HP HN P0 B0 S16 IDX B3 HE ELO EHI BIG RSV RB0r RE0 NR SC NOM MOVE.
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  st1. st1. st1. st1. st1. st1. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by lia. fold rsv0.
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    apply (rrealloc_t2b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P E rsv n sc HP HN P0 ELO EHI RSV ltac:(lia) RB0r RE0 NR SC NOM MOVE).
  - (* [comment removed for export] *)
    destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read ctusegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (B + stride * idx + 16 + stride + -8) in RD4 by lia.
    pose proof (bytes_at_read ctusegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (B + stride * idx + 16 + stride + -9) in RD5 by lia.
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite zx32_wz' by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    apply (rrealloc_t2b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P E rsv n sc HP HN P0 ELO EHI RSV ltac:(lia) RB0r RE0 NR SC NOM MOVE).
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t1s : forall ra sp gp tp t1 s0 s1 a0 a1 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (P B E idx b3 r32 n sc : Z),
  let stride := 16 * size_class sc in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  sc < 48 ->
  ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))) ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> 0 <= B -> 16 <= stride -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  E = B + 16 + stride * idx + stride - 4 -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  0 <= n < 2^32 -> 0 <= sc < 64 -> (n < 131052 \/ sc < 48) -> E - P < n ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (E - rsv) F fc m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) t1 (Z_to_bv 64 (sc * 2)) s0 s1 a0 a1 (wz B) (wz sc) a4 (Z_to_bv 64 467628) a6 (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b50c4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros stride rsv0 rsv SC48 RS HP HN P0 B0 S16 IDX B3 HE ELO EHI BIG RSV RB0r RE0 NR SC NOM MOVE.
  assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (unfold stride; f_equal; lia).
  apply (rrealloc_t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P B E stride idx b3 r32 n sc HP HN P0 B0 S16 IDX B3 HE ELO EHI BIG RSV RB0r RE0 NR SC NOM MOVE).
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t1 : forall ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (P B idx b3 r32 n sc off16 last_idx freeable maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc in
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> 0 <= B -> 16 <= stride -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  0 <= n < 2^32 -> 0 <= sc < 64 -> (n < 131052 \/ sc < 48) -> E - P < n ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (E - rsv) F fc m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 s1 a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 467628) (wz off16) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b50a8) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until maplen. intros mword stride E rsv0 rsv RS O16 LI FB ML Hml SC48 HP HN P0 B0 S16 IDX B3 ELO EHI BIG RSV RB0r RE0 NR SC NOM MOVE.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (STR : stride = 16 * size_class sc).
    { unfold stride. rewrite (proj2 (Z.eqb_eq _ _) K), andb_false_r. reflexivity. }
    eapply rrealloc_t1s with (P:=P) (B:=B) (E:=E) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc);
      [exact (SC48 (or_introl K))| exact (RS (SC48 (or_introl K)))| exact HP| exact HN| exact P0| exact B0| rewrite <- STR; exact S16| exact IDX| exact B3
      | unfold E; rewrite STR; reflexivity| exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0| exact NR| exact SC| exact NOM| exact MOVE].
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. specialize (Hml K). lia. }
    (* [comment removed for export] *)
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      assert (STR : stride = 4096 * maplen - 16).
      { unfold stride. rewrite (proj2 (Z.eqb_eq _ _) K3). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). reflexivity. }
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
      eapply rrealloc_t2 with (P:=P) (B:=B) (E:=E) (stride:=stride) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc);
        [exact HP| exact HN| exact P0| exact B0| exact S16| exact IDX| exact B3| reflexivity| exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0| exact NR| exact SC| exact NOM| exact MOVE].
    + (* [comment removed for export] *)
      assert (STR : stride = 16 * size_class sc).
      { unfold stride. rewrite (proj2 (Z.eqb_neq _ _) K3). reflexivity. }
      eapply rrealloc_t1s with (P:=P) (B:=B) (E:=E) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc);
        [exact (SC48 (or_intror K3))| exact (RS (SC48 (or_intror K3)))| exact HP| exact HN| exact P0| exact B0| rewrite <- STR; exact S16| exact IDX| exact B3
        | unfold E; rewrite STR; reflexivity| exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0| exact NR| exact SC| exact NOM| exact MOVE].
Qed.

Lemma rrealloc_hdr_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A n : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc in
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes ctusegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (* [comment removed for export] *)
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  16 <= stride -> 0 <= B -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  (* [comment removed for export] *)
  0 <= n < 2^32 -> E - P < n -> (n < 131052 \/ sc < 48) ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (E - rsv) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b4fb4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros idx mword stride E rsv0 rsv HP HN AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 B0 ELO EHI BIG RSV RB0r RE0 NR MOVE NOMREMAP.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes ctusegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (P0 : 0 <= P) by lia.
  assert (TAIL : forall x1 x28 x29 x8 x9 x18,
    evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (E - rsv) F fc m)
      (MS (mkR x1 sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) x8 x9 a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 467628) (wz off16) (wz b3) x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6) F (Z_to_bv 64 0x2b50a8) fc None m (seg_rom ctusegs))).
  { intros. eapply rrealloc_t1 with (P:=P) (B:=B) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc) (off16:=off16) (last_idx:=last_idx) (freeable:=freeable) (maplen:=maplen);
      [exact RS| exact O16| exact LI| exact FB| exact ML| exact Hml| exact SC48| exact HP| exact HN| exact P0| exact B0| exact S16| exact IDX| exact B3
      | exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0| exact NR| exact SC| exact NOMREMAP| exact MOVE]. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *)
    specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    rewrite GW. apply TAIL.
  - (* [comment removed for export] *)
    assert (SCLT : sc < 48) by (rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia).
    specialize (RS SCLT). specialize (Hsc SCLT).
    assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. apply TAIL.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_hdr_walk_eq : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (P G B A n : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word) (stride E rsv s2v : Z),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc) ->
  E = B + 16 + stride * idx + stride - 4 ->
  rsv = (if 160 <=? b3 then r32 else Z.shiftr b3 5) ->
  s2v = E - rsv ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes ctusegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  16 <= stride -> 0 <= B -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> Z.shiftr b3 5 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  0 <= n < 2^32 -> E - P < n -> (n < 131052 \/ sc < 48) ->
  evt ctusegs (rrealloc_hdr_post sp gp tp a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 s2v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b4fb4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until s2v. intros idx mword -> -> -> ->. intros.
  eapply rrealloc_hdr_walk with (P:=P) (G:=G) (B:=B) (A:=A) (n:=n) (b3:=b3) (off16:=off16) (avail:=avail) (freed:=freed)
    (last_idx:=last_idx) (freeable:=freeable) (sc:=sc) (maplen:=maplen) (secret:=secret) (r32:=r32) (prev:=prev) (next:=next); eassumption.
Qed.
End WithCeiling0.
