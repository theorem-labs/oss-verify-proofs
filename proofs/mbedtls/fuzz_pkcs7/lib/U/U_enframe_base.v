(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import ListFacts CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk BBFrame MemcpyLib AgentLib MallocDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import EnframeArith.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_enframe_base () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BB.MallocDefs.slack_of"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BB.MallocDefs.res_code"].


Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SCT : Z := 0x170fc.

(* [comment removed for export] *)
Definition sc_entry (sc : Z) : list byte :=
  match rdn RSEGS (fun _ => None) (Z_to_bv 64 (SCT + 2 * sc)) 2 with Some bs => bs | None => [] end.



(* [comment removed for export] *)
Definition sc_tbl_clear (m : word -> option byte) : Prop :=
  forall j, (0 <= j < 96)%Z -> m (Z_to_bv 64 (SCT + j)) = None.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac solve_kcs :=
  repeat (apply keeps_cs_upd; [| not_kept]); first [apply keeps_cs_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record efH (mem : word -> option byte) (c : word)
       (g M W idx n h3 o16 stride start off : Z) : Prop := EFH {
  Estride : stride = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W);
  Estart  : start = slot_start M stride idx;
  Eoff    : off = enframe_off (slack_of stride n)
                    ((if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256);
  Hg      : 0 <= g /\ g + 40 <= 2 ^ 64;
  HM      : 0 <= M;
  HW      : 0 <= W < 2 ^ 64;
  Hidx    : 0 <= idx < 32;
  Hn      : 0 <= n /\ n + 4 <= stride;
  Hsc     : (w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48;
  Hst31   : stride < 2 ^ 31;
  Hq      : stride * idx + 4096 <= 16 * 65536;
  Hnw     : start + stride < 2 ^ 64;
  Hdisj   : g + 24 <= start - 3 \/ start + stride - 4 <= g + 16;
  Hh3     : 0 <= h3 < 256;
  Ho16    : 0 <= o16 < 65536;
  RM      : rdn RSEGS mem (Z_to_bv 64 (g + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  RW      : rdn RSEGS mem (Z_to_bv 64 (g + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  R4      : mem (Z_to_bv 64 (start - 4)) = Some (Z_to_bv 8 0);
  R3      : mem (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 h3);
  R2      : h3 <> 0 ->
            rdn RSEGS mem (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 o16));
  OK      : store_ok RSEGS mem (Z_to_bv 64 (start - 3)) (Z.to_nat (stride - 1)) = true;
  TBL     : sc_tbl_clear mem }.

(* [comment removed for export] *)
Record enframe_post (mem' : word -> option byte) (idx n stride start off : Z) : Prop := EPOST {
  P_p := start + 16 * off;
  P_e := start + stride - 4;
  P_r := stride - 4 - n - 16 * off;
  P_q := stride * idx / 16 + off;
  Pm4   : mem' (Z_to_bv 64 (P_p - 4)) = Some (Z_to_bv 8 0);
  Pm3   : mem' (Z_to_bv 64 (P_p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code P_r));
  Pm2   : rdn RSEGS mem' (Z_to_bv 64 (P_p - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 P_q));
  Pzr   : 0 < P_r -> mem' (Z_to_bv 64 (P_p + n)) = Some (Z_to_bv 8 0);
  Pe5   : 5 <= P_r -> mem' (Z_to_bv 64 (P_e - 5)) = Some (Z_to_bv 8 0);
  Pe4   : 5 <= P_r -> rdn RSEGS mem' (Z_to_bv 64 (P_e - 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 P_r));
  Ps3   : off <> 0 -> mem' (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224);
  Ps2   : off <> 0 -> rdn RSEGS mem' (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 off));
  Pr    : 0 <= P_r /\ 0 <= off <= 255 /\ 0 <= P_q < 65536 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  #[using="mem0 c g M W idx n h3 o16 start off H"] Lemma stride_facts : 16 <= stride /\ stride mod 16 = 0 /\ stride < 2 ^ 31.
  Proof.
    destruct H. clear RM0 RW0 R5 R6 R7 OK0 TBL0.
    assert (Hml : 0 <= w_maplen W) by (unfold w_maplen; apply Z.div_pos; lia).
    rewrite Estride0 in *. unfold slot_stride, UNIT in *.
    destruct (negb (w_maplen W =? 0) && (w_lastidx W =? 0))%bool eqn:E.
    - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E2.
      destruct (w_maplen W =? 0) eqn:E3; [discriminate|]. apply Z.eqb_neq in E3.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      repeat split; lia.
    - assert (Hs : w_sizeclass W < 48).
      { apply Hsc0. destruct (w_maplen W =? 0) eqn:E3.
        + left. apply Z.eqb_eq, E3.
        + right. cbn in E. apply Z.eqb_neq. exact E. }
      assert (0 <= w_sizeclass W) by (unfold w_sizeclass; apply Z.mod_pos_bound; lia).
      pose proof (size_class_pos (w_sizeclass W) ltac:(lia)).
      repeat split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  #[using="mem0 c g M W idx h3 o16 start H"] Lemma off_facts : ltac2:(CDefT.buildp (gd_tbl_P_enframe_base ()) "(0.(0.(1.=Voff,)(1.Voff,(2.Vstride,Vn,)))(0.(1.Voff,+??.)(0.(1.(3.+10.Voff,)(4.(4.Vstride,+4.)Vn,))(1.=(2.Vstride,Vn,)))))")
(* [comment removed for export] *).
  Proof.
    destruct H. clear RM0 RW0 R5 R6 R7 OK0 TBL0.
    pose proof (u64_range c).
    assert (Hsl : 0 <= slack_of stride n /\ 16 * slack_of stride n <= stride - 4 - n).
    { unfold slack_of, IB, UNIT.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; [apply Z.div_pos; lia|]. lia. }
    assert (Ho0 : 0 <= (if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256 < 256)
      by (apply Z.mod_pos_bound; lia).
    pose proof (enframe_off_le (slack_of stride n) _ (proj1 Hsl) Ho0) as B.
    rewrite <- Eoff0 in B.
    pose proof (enframe_off_255 (slack_of stride n) _ (proj1 Hsl) Ho0) as B2.
    rewrite <- Eoff0 in B2.
    repeat split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac greg :=
  repeat match goal with
         | Hr : getr ?rs ?k = ?v |- context [getr ?rs ?k] => rewrite Hr
         end.

(* [comment removed for export] *)
Ltac stb F D aa bb vtac oktac :=
  chain_step;
  [ reflexivity
  | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; reflexivity | vtac | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac sth F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sh_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; first [ reflexivity | assumption ] | oktac ]
  | step_simpl ].

Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sw_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; first [ reflexivity | assumption ] | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac ldbu F D rtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu; [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac ldhu F D vv rtac btac :=
  chain_step;
  [ reflexivity
  | eapply step_lhu with (v := vv); [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac | btac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac ldd F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv); [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac
    | apply bytes_le_to_Z_8 ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)



(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memT := word -> option byte.

(* [comment removed for export] *)
Definition mD (start off : Z) (m : memT) : memT :=
  if off =? 0 then m else
  wbytes (wbytes (wbytes m (Z_to_bv 64 (start - 3)) [Z_to_bv 8 224])
                 (Z_to_bv 64 (start - 2)) (word_to_le_bytes 2 (Z_to_bv 64 off)))
         (Z_to_bv 64 (start + 16 * off - 4)) [Z_to_bv 8 0].

(* [comment removed for export] *)
Definition mE1 (idx stride start off : Z) (m : memT) : memT := ltac2:(CDefT.buildp (gd_tbl_P_enframe_base ()) "(5.(5.O1.(6.&40.(4.(7.O3.(3.+10.O2.))+3.))(8.(9.&8.)(6.&8.O5.)(:.(9.&8.))))(6.&40.(4.(7.O3.(3.+10.O2.))+2.))(;.#2.(6.&40.(7.(<.(3.O4.O5.)+10.)O2.))))")
(* [comment removed for export] *).

Definition mE (idx n stride start off : Z) (m : memT) : memT :=
  let r := stride - 4 - n - 16 * off in
  let m1 := mE1 idx stride start off m in
  if r =? 0 then m1 else
  let m2 := wbytes m1 (Z_to_bv 64 (start + 16 * off + n)) [Z_to_bv 8 0] in
  if r <? 5 then m2 else
  wbytes (wbytes m2 (Z_to_bv 64 (start + stride - 4 - 5)) [Z_to_bv 8 0])
         (Z_to_bv 64 (start + stride - 4 - 4)) (word_to_le_bytes 4 (Z_to_bv 64 r)).

(* [comment removed for export] *)
Definition mF (idx n stride start off : Z) (m : memT) : memT := ltac2:(CDefT.buildp (gd_tbl_P_enframe_base ()) "(5.O1.(6.&40.(4.(7.O3.(3.+10.O2.))+3.))(8.(9.&8.)(6.&8.(7.O6.(3.+20.(=.(4.(4.(4.O4.+4.)O5.)(3.+10.O2.))))))(:.(9.&8.))))")
(* [comment removed for export] *).




