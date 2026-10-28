(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_C9_ctrl.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ARD_RA_READ : Z := 0x5562a0.    (* [comment removed for export] *)
Definition ARD_RA_TF1 : Z := 0x5563a8.     (* [comment removed for export] *)
Definition ARD_RA_DU : Z := 0x55677c.      (* [comment removed for export] *)
Definition ARD_RA_MC : Z := 0x5567f4.      (* [comment removed for export] *)
Definition ARD_RA_TF2 : Z := 0x5562c4.     (* [comment removed for export] *)
Definition ARD_RA_DF : Z := 0x556304.      (* [comment removed for export] *)
Definition ARD_RA_DI2 : Z := 0x556324.     (* [comment removed for export] *)
Definition ARD_HEAD : Z := 0x55624c.
Definition ARD_EXIT : Z := 0x556a14.
Definition ASHB : Z := 2147450880.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ardslots (ctx fbase ff vret mb a nump : Z) (w104 w128 j136 j152 w216 w224 w240 : word) (j256 : list byte) : list cell :=
  [C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.shiftr ctx 3 + ASHB)); C8 w104; C8 w128; C8 (Z_to_bv 64 (ctx + 4));
   C8 (Z_to_bv 64 (Z.shiftr fbase 3 + ASHB)); C8 (Z_to_bv 64 fbase); C8 j136; C8 j152; C8 (Z_to_bv 64 vret); C8 w216; C8 w240; C8 (Z_to_bv 64 mb);
   C8 (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)); C8 w224; C8 (Z_to_bv 64 (ctx + 32)); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (Z.shiftr (ctx + 24) 3 + ASHB));
   C8 (Z_to_bv 64 (ctx + 40)); C8 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)); C8 (Z_to_bv 64 (ctx + 24)); C8 (Z_to_bv 64 (ctx + 8)); C8 (Z_to_bv 64 ff);
   C8 (Z_to_bv 64 (ctx + 12)); C8 (Z_to_bv 64 nump); C8 (Z_to_bv 64 (ctx + 1542)); C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 (Z.lxor (ctx + 1542) 18446744073709551615));
   C8 (Z_to_bv 64 (ctx + 1542)); CB 16 j256; C8 (Z_to_bv 64 fbase)].
(* [comment removed for export] *)
Definition ardsaves (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : list cell :=
  [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].
(* [comment removed for export] *)
Definition rdhdr (bl bo tl c enc : Z) : list cell :=
  [C4 (wz bl); C4 (wz bo); C4 (wz tl); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz enc)].

(* [comment removed for export] *)
Lemma unsigned_neg64 : forall c, - 2^64 <= c < 0 -> bv_unsigned (Z_to_bv 64 c) = c + 2^64.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  replace c with ((c + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma land64_neg : forall k, - 2^64 <= k < 0 -> Z.land k 18446744073709551615 = k + 2^64.
Proof.
  intros k Hk. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  replace k with ((k + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma land64_nonneg : forall k, 0 <= k < 2^64 -> Z.land k 18446744073709551615 = k.
Proof. intros k Hk. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma c9_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma c9_le8_split : forall x, 0 <= x < 2^64 -> le8 (wz x) = le4 (wz x) ++ le4 (wz (Z.shiftr x 32)).
Proof.
  intros x Hx. unfold le8, le4, word_to_le_bytes, wz. rewrite !unsigned_lit; [|split; [apply Z.shiftr_nonneg; lia|]|lia].
  2:{ rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. change (2^32*2^64) with (2^96). lia. }
  change 8%nat with (4 + 4)%nat at 1. rewrite c9_le_bytes_add. reflexivity.
Qed.

Lemma c9_C8_split : forall m A pre x post, 0 <= x < 2^64 ->
  rw_cells asegs m A (pre ++ C8 (wz x) :: post) -> rw_cells asegs m A (pre ++ C4 (wz x) :: C4 (wz (Z.shiftr x 32)) :: post).
Proof.
  intros m A pre x post Hx. unfold rw_cells, cells_at.
  rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite (c9_le8_split x Hx), <- app_assoc. cbn [app].
  replace (8 + cells_size post)%nat with (4 + (4 + cells_size post))%nat by lia. tauto.
Qed.

Ltac c8split H x :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let rec find l :=
        lazymatch l with
        | C8 (Z_to_bv 64 x) :: ?post => constr:((@nil cell, post))
        | ?c :: ?rest => let r := find rest in lazymatch r with (?p, ?q) => constr:((c :: p, q)) end
        end in
      let r := find cs in
      lazymatch r with
      | (?pre, ?post) =>
          change cs with (pre ++ C8 (wz x) :: post) in H;
          apply c9_C8_split in H; [cbn [app] in H; unfold wz in H | lia]
      end
  end.

Ltac ld4 H x := let H4 := fresh "H4" in pose proof H as H4; c8split H4 x; st1; clear H4.
Ltac lxor_kill K :=
  exfalso; match type of K with context [Z.lxor ?x ?y] =>
    pose proof (proj2 (Z.lxor_nonneg x y) ltac:(split; intros; lia)); lia end.
Ltac reacc_c ACC MU NSW ACC2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ACC2 : accessible mx _ 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW]) end.
Ltac at_load := lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with Some ?w => let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (Load _ _ _ _ _, _) => idtac | _ => fail end end end.
Ltac ckauto ACC MU NSW :=
  let A := fresh "ACCa" in
  at_load; reacc_c ACC MU NSW A;
  match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => match R with context [Z.shiftr ?X 3] => ck8_load A X end end;
  clear A.
Ltac kill_any K :=
  first [ (exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia)
        | (apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia)
        | (apply Bool.andb_true_iff in K; let K' := fresh K in destruct K as [K K']; apply Z.ltb_lt in K; apply Z.ltb_lt in K'; exfalso; revert K K'; rewrite ?unsigned_lit, ?signed_lit by lia; lia)
        | (exfalso; repeat match goal with H : context [Z.land ?v 18446744073709551615] |- _ =>
             first [rewrite (land64_neg v) in H by lia | rewrite (land64_nonneg v) in H by lia] end; lia) ].
Ltac dec_lia :=
  let K := fresh "KD" in
  lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
    first [ (if_cases K; zify_cond K; [kill_any K | try clear K])
          | (if_cases K; zify_cond K; [try clear K | kill_any K]) ] end.
Ltac ld4any := at_load;
  match goal with H : rw_cells _ _ _ ?cs |- _ => match cs with context [C8 (Z_to_bv 64 ?x)] => ld4 H x end end.
Ltac nrm_ub := repeat (match goal with
  | |- evt _ _ (MS ?R _ ?pc _ _ _ _) => match constr:((R, pc)) with
      | context [sx32 (Z_to_bv 64 ?x)] => rewrite (ECH_C9_ctrl.sx32_wz_small x) by lia
      | context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia
      | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
      | context [?x + 0] => rewrite (Z.add_0_r x)
      | context [v_sltu ?x ?y] => rewrite (v_sltu_b2z x y)
      | context [v_slti ?x ?i] => rewrite (v_slti_b2z x i)
      | context [v_slt ?x ?y] => rewrite (v_slt_b2z x y)
      | context [v_sltiu ?x ?i] => rewrite (v_sltiu_b2z x i)
      | context [Z.lxor ?x (2^63)] => rewrite (zb_lxor_sign x) by lia
      | context [Z.b2z (?x <? ?y)] =>
          first [ rewrite (proj2 (Z.ltb_lt x y)) by (rewrite ?Z.mod_small by lia; lia)
                | rewrite (proj2 (Z.ltb_ge x y)) by (rewrite ?Z.mod_small by lia; lia) ]; cbn [Z.b2z]
      | context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
      end end).
Ltac nrm_hyp H := repeat (match type of H with
  | context [sx32 (Z_to_bv 64 ?x)] => rewrite (ECH_C9_ctrl.sx32_wz_small x) in H by lia
  | context [bv_swrap 32 ?x] => rewrite (swrap32_small x) in H by lia
  | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in H by lia
  | context [?x + 0] => rewrite (Z.add_0_r x) in H
  end).
Ltac gox ACC MU NSW := repeat (go; first [ckauto ACC MU NSW | ld4any | progress nrm_ub | dec_lia]); go.
Ltac goxto ACC MU NSW P := repeat (go_to P; tryif at_pc P then fail else first [ckauto ACC MU NSW | ld4any | progress nrm_ub | dec_lia]); go_to P.
Ltac reacc_n ACC MU NSW N ACC2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ACC2 : accessible mx _ N) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW]) end.
Ltac ckauto_n ACC MU NSW N :=
  let A := fresh "ACCa" in
  at_load; reacc_n ACC MU NSW N A;
  match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => match R with context [Z.shiftr ?X 3] => ck8_load A X end end;
  clear A.
Ltac gox2 A1 N1 A2 N2 MU NSW := repeat (go; first [ckauto_n A1 MU NSW N1 | ckauto_n A2 MU NSW N2 | ld4any | progress nrm_ub | dec_lia]); go.
Ltac goxto2 A1 N1 A2 N2 MU NSW P := repeat (go_to P; tryif at_pc P then fail else first [ckauto_n A1 MU NSW N1 | ckauto_n A2 MU NSW N2 | ld4any | progress nrm_ub | dec_lia]); go_to P.

Local Ltac ubal_any :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch R with
      | context [Z.land ?x 7] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | idtac ]
      | context [Z.land ?x 3] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 4 = 0 |- _ => ubal_by H end
                | idtac ]
      | _ => idtac
      end
  | _ => idtac
  end.



Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac killb K :=
    first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; apply Z.ltb_lt in K'; exfalso; revert K K'; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia ].

  (* [comment removed for export] *)
  Lemma ard_head :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      0 < c < 2^31 -> 0 <= out < 2^64 -> 0 <= outl < 2^64 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_READ) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 mb) (Z_to_bv 64 (ctx + 1542)) (Z_to_bv 64 1024) a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 mb) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros C OUT OUTL CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_HEAD, ARD_RA_READ, P_BIO_read, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. go.
    (* [comment removed for export] *)
    reacc_c ACC MU NSW0 ACC1. ck8_check ACC1 (ctx + 24). go.
    (* [comment removed for export] *)
    rewrite (ECH_C9_ctrl.sx32_wz_small c) by lia. if_cases K; zify_cond K; [first [killb K | kill K]|]. try clear K. go.
    (* [comment removed for export] *)
    ck8_check ACC1 (ctx + 8). go. rewrite ?(sx32_lit 0) by lia. go.
    if_cases K2; zify_cond K2; [lxor_kill K2|]. try clear K2. go. step.
    finish.
    all: match goal with |- ?G => idtac "HEAD-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_head_exit :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      - 2^31 <= c <= 0 -> 0 <= out < 2^64 -> 0 <= outl < 2^64 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros C OUT OUTL CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_HEAD, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    (* [comment removed for export] *)
    reacc_c ACC MU NSW0 ACC1. go. ck8_check ACC1 (ctx + 24). go.
    (* [comment removed for export] *)
    rewrite (ECH_C9_ctrl.sx32_wz_small c) by lia. if_cases K; zify_cond K.
    2:{ exfalso. destruct (Z.lt_ge_cases c 0); [rewrite land64_neg in * by lia | rewrite land64_nonneg in * by lia]; lia. }
    try clear K. go_to ARD_EXIT.
    (* [comment removed for export] *)
    idtac.
    finish.
    all: match goal with |- ?G => idtac "HEADX-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_data1 :
    forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s4 s2 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n bl bo c enc lo : Z),
      0 < n <= 1024 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_TF1) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 a) (Z_to_bv 64 (-1)) (Z_to_bv 64 ctx) a3 a4 a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 12)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_test_flags) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo n c enc))
        (MS (mkR (Z_to_bv 64 ARD_RA_READ) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 mb) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_READ) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros N CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_READ, ARD_RA_TF1, P_BIO_test_flags, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. go. if_cases K; zify_cond K; [| first [killb K | kill K]]; try clear K.
    reacc_c ACC MU NSW0 ACC1. go. ck8_check ACC1 (ctx + 8). go.
    rewrite ?(sx32_lit 0) by lia. rewrite ?unsigned_lit by lia.
    replace (bv_swrap 32 (n + 0)) with n by (rewrite Z.add_0_r, swrap32_small by lia; reflexivity). go.
    ck8_check ACC1 (ctx + 8). go.
    reacc_c ACC MU NSW0 ACC2. ck8_load ACC2 (ctx + 20). clear ACC1. go. step.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    finish.
    all: match goal with |- ?G => idtac "D1-LEFT:" G end.
  Qed.

  Local Ltac reacc ACC MU NSW AC2 :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AC2 : accessible mx _ 2584) by (eapply accessible_across2; [exact ACC| exact MU| exact NSW]) end.

  (* [comment removed for export] *)
  Lemma ard_data2 :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n fl bl bo c enc lo : Z),
      0 <= fl < 2^31 -> Z.land fl BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo n c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DU) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 enc) (Z_to_bv 64 (ctx + 40)) (Z_to_bv 64 ctx) (Z_to_bv 64 (ctx + 1542)) (Z_to_bv 64 n) a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 0) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeUpdate) fc None m1 (seg_rom asegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 0) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_TF1) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FL NONL CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_TF1, ARD_RA_DU, P_EVP_DecodeUpdate, B64CTX_SIZE, BIO_FLAGS_BASE64_NO_NL, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. go. rewrite NONL. go.
    reacc_c ACC MU NSW0 ACC1. ck8_load ACC1 (ctx + 8). go.
    reacc_c ACC MU NSW0 ACC2. ck8_load ACC2 (ctx + 32). clear ACC1. go. step.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    finish.
    all: match goal with |- ?G => idtac "D2-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_du_neg :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n k bl bo c enc lo : Z),
      - 2^31 <= k < 0 -> 0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 4)) (Z_to_bv 64 ctx) a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB)) (Z_to_bv 64 vret) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 (Z_to_bv 64 0) j256)
          /\ rw_cells asegs m1 ctx (rdhdr 0 0 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 0) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DU) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros K CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DU, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. goxto ACC MU NSW0 ARD_EXIT.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    rewrite ?Z.land_0_l in SL. rewrite ?Z.land_0_l.
    finish.
    all: match goal with |- ?G => idtac "DUN-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_du_pos :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump n k bl bo c enc lo : Z),
      0 <= k < 2^31 -> 0 <= bl < 2^31 -> 0 < outl < 2^31 -> 0 <= out < 2^64 ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_MC) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 out) (Z_to_bv 64 (ctx + 40)) (Z_to_bv 64 (Z.min bl outl)) (Z_to_bv 64 (ctx + 4)) (Z_to_bv 64 ctx) a5 a6 a7
                 (Z_to_bv 64 bl) (Z_to_bv 64 (Z.min bl outl)) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB)) (Z_to_bv 64 vret) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl 0 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 0) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr (ctx + 20) 3 + ASHB)) (Z_to_bv 64 n) (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DU) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros K BL OUTL OUT CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DU, ARD_RA_MC, AASAN_MEMCPY, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. gox ACC MU NSW0.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - (* [comment removed for export] *) replace (Z.min bl outl) with bl by lia.
      (* [comment removed for export] *)
      gox ACC MU NSW0. step. finish.
    - (* [comment removed for export] *) replace (Z.min bl outl) with outl by lia.
      gox ACC MU NSW0. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_mc_loop :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl ret nump bl k enc lo : Z),
      0 <= bl < outl -> outl < 2^31 -> 0 <= ret -> ret + outl < 2^31 -> 0 < out -> out + outl <= 2^64 ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff ret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl 0 0 k enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 (outl - bl)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 4)) a4 a5 a6 a7 (Z_to_bv 64 bl) (Z_to_bv 64 (bl + out)) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_HEAD) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff (ret + bl) mb a nump (Z_to_bv 64 (bl + out)) (Z_to_bv 64 (outl - bl)) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr 0 0 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 bl) (Z_to_bv 64 bl) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB)) (Z_to_bv 64 ret) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_MC) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BL OUTL RET RETO OUT OUTO CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_MC, ARD_HEAD, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. goxto ACC MU NSW0 ARD_HEAD.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    nrm_hyp SL.
    finish.
    all: match goal with |- ?G => idtac "MCL-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_mc_done :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl ret nump bl k enc lo : Z),
      0 < outl <= bl -> bl < 2^31 -> 0 <= ret -> ret + outl < 2^31 -> 0 < out -> out + outl < 2^64 ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff ret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl 0 0 k enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ctx + 4)) a4 a5 a6 a7 (Z_to_bv 64 bl) (Z_to_bv 64 (outl + out)) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff (ret + outl) mb a nump (Z_to_bv 64 (outl + out)) (Z_to_bv 64 0) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr (if bl =? outl then 0 else bl) (if bl =? outl then 0 else outl) 0 k enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 bl) (Z_to_bv 64 outl) (Z_to_bv 64 (Z.shiftr (ctx + 4) 3 + ASHB)) (Z_to_bv 64 ret) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_MC) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BL BLH RET RETO OUT OUTO CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_MC, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. gox ACC MU NSW0.
    (* [comment removed for export] *)
    idtac.
    if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - (* [comment removed for export] *)
      replace (bl =? outl) with false by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      goxto ACC MU NSW0 ARD_EXIT. nrm_hyp SL. nrm_hyp HD. rewrite ?Z.sub_diag in SL. rewrite ?Z.sub_diag.
      finish.
    - (* [comment removed for export] *)
      replace (bl =? outl) with true by (symmetry; apply Z.eqb_eq; lia).
      (* [comment removed for export] *)
      goxto ACC MU NSW0 ARD_EXIT.
      (* [comment removed for export] *)
      nrm_hyp SL. nrm_hyp HD. rewrite ?Z.sub_diag in SL. rewrite ?Z.sub_diag.
      finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof1 :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s8 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_TF2) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 mb) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 mb) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_test_flags) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 mb) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) s8 s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_READ) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros CP CL SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_READ, ARD_RA_TF2, P_BIO_test_flags, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    idtac. go. step.
    (* [comment removed for export] *)
    idtac.
    finish.
    all: match goal with |- ?G => idtac "EOF1-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof1b :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump bl bo c enc lo : Z),
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DF) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 enc) (Z_to_bv 64 0) (Z_to_bv 64 nump) a3 a4 a5 a6 a7 (Z_to_bv 64 (ctx + 32)) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0) (Z_to_bv 64 mb) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_TF2) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_TF2, ARD_RA_DF, P_EVP_DecodeFinal, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    idtac. gox ACC MU NSW0. step.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    idtac.
    finish.
    all: match goal with |- ?G => idtac "EOF1B-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof2 :
    forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump rv bl bo c enc lo : Z),
      (rv = -1 \/ rv = 1) ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ARD_RA_DI2) (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 enc) (Z_to_bv 64 enc) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (if rv <? 0 then -1 else 0)) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeInit) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (ctx + 32)) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DF) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros RV CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DF, ARD_RA_DI2, P_EVP_DecodeInit, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac.
    (* [comment removed for export] *)
    destruct RV as [-> | ->].
    - gox ACC MU NSW0. step. replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity). finish.
    - gox ACC MU NSW0. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ard_eof3 :
    forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 s10 t3 t4 t5 t6 : word) (j136 j152 w216 w224 w240 : word) (j256 : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sp0 fb ctx fbase ff mb a out outl vret nump rc bl bo c enc lo : Z),
      (rc = -1 \/ rc = 0) ->
      0 < ctx -> ctx mod 16 = 0 -> ctx + B64CTX_SIZE <= lo -> aapp ctx B64CTX_SIZE ->
      accessible m ctx B64CTX_SIZE ->
      rw_cells asegs m (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 w240 j256) ->
      rw_cells asegs m ctx (rdhdr bl bo 0 c enc) ->
      stk asegs m lo fb -> aceil <= lo -> lo <= fb -> 0 <= fb -> fb + 280 <= sp0 -> sp0 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) (Z_to_bv 64 0) (Z_to_bv 64 rc) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 rc) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                   F (Z_to_bv 64 ARD_EXIT) fc None m1 (seg_rom asegs)
          /\ munch [(fb, fb + 280); (ctx, ctx + 40)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo fb
          /\ rw_cells asegs m1 (fb + 8) (ardslots ctx fbase ff vret mb a nump (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 (Z_to_bv 64 rc) j256)
          /\ rw_cells asegs m1 ctx (rdhdr bl bo 0 rc enc))
        (MS (mkR ra (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 rc) (Z_to_bv 64 (Z.shiftr (ctx + 32) 3 + ASHB)) s4 (Z_to_bv 64 (Z.shiftr (ctx + 8) 3 + ASHB)) (Z_to_bv 64 (ctx + 8)) (Z_to_bv 64 (ctx + 20)) (Z_to_bv 64 0) s9 s10 (Z_to_bv 64 ASHB) t3 t4 t5 t6)
            F (Z_to_bv 64 ARD_RA_DI2) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros RC CP CAL CL CAP ACC SL HD ST CEIL LO FB0 FBT SPT MI. acb.
    unfold ARD_RA_DI2, ARD_EXIT, B64CTX_SIZE, ASHB in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(fb, fb + 280); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _). unfold AAPP_HI in AHIc.
    unfold ardslots, ASHB in SL. unfold rdhdr, wz in HD |- *.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(fb, fb + 280); (ctx, ctx + 40)]) by nsw_tac.
    (* [comment removed for export] *)
    idtac. goxto ACC MU NSW0 ARD_EXIT.
    (* [comment removed for export] *)
    idtac.
    rewrite ?(sx32_lit 0) by lia.
    finish.
    all: match goal with |- ?G => idtac "EOF3-LEFT:" G end.
  Qed.
End S.
