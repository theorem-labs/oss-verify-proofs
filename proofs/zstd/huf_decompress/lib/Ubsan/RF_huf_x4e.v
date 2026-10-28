(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_fargs RF_huf_fdw_tk RF_huf_x2t_fr RF_huf_x4fin RF_huf_x4fin3 RF_huf_x4body_iface RF_huf_x4fast.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Ltac wsrd A i :=
  lazymatch goal with W : u64arr usegs ?mm A ?ws |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_read usegs mm A ws i _ _ W eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) end.
Definition x4e_rng (z : Z) : bool := let o := z - 0x16e6c in
  ((0 <=? o) && (o <=? 404)) || ((2516 <=? o) && (o <? 2544)) || ((5116 <=? o) && (o <? 5120)) || ((5180 <=? o) && (o <? 5252)).
Ltac x4e_to o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in ((z =? 0x16e6c + o) || negb (x4e_rng z))%bool in
      lazymatch d with true => fail | false => zstep end
  | _ => zstep end).
Ltac x4e_ck U := exfalso; first [ discriminate U | congruence |
  repeat (first [ rewrite signed_lit in U by lia | rewrite unsigned_lit in U by lia ]); lia ].
Ltac x4e_br := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
  let U := fresh "CK" in
  first [ if_cases U; zify_cond U; [ x4e_ck U | ] | if_cases U; zify_cond U; [ | x4e_ck U ] ] end.
Ltac x4e_split := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
  let U := fresh "BR" in if_cases U; zify_cond U end.
Ltac x4e_walk o := x4e_to o; repeat (x4e_br; x4e_to o); try (x4e_split; x4e_walk o).


Section CANSEC1. Context {rc : runConstT}.
Section X4E.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DTA : DT mod 4 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition X4S (mm : fmem) : Prop :=
    (exists buf, u8arr usegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at usegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at usegs mm (DT + 4) cbs
    /\ bytes_at usegs mm DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk usegs mm lo (SP + -104)
    /\ rw_cells usegs mm (SP + -104) FRS
    /\ mem_inv usegs mm /\ munch DW m0 mm /\ wmono usegs m0 mm.

  (* [comment removed for export] *)
  Hypothesis SLOW : forall mm (xra t0 t1 t2 x9 a0 a1 a2 a6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    X4S mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 (Z_to_bv 64 SS) x9 a0 a1 a2
                           (Z_to_bv 64 n) (Z_to_bv 64 DT) (Z_to_bv 64 DST) a6 (Z_to_bv 64 dcap)
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1785c) fc None mm (seg_rom usegs)).
  Hypothesis BODY : x4_body_stmt.

  (* [comment removed for export] *)
  Lemma x4e_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk usegs mm lo (SP + -104) -> rw_cells usegs mm (SP + -104) FRS ->
    mem_inv usegs mm -> munch DW m0 mm -> wmono usegs m0 mm ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1826c) fc None mm (seg_rom usegs)).
Proof using All.
    intros until xra. intros ST FR MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    do 14 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma m7_rd : forall m1, mem_inv usegs m1 ->
    ov_read_bytes usegs m1 (Z_to_bv 64 0x10470) 8 = Some (le8 (Z_to_bv 64 2635249153387078803)).
Proof using All.
    intros m1 MI.
    assert (RC : ro_cells usegs m1 0x10470 [CB (length (le8 (Z_to_bv 64 2635249153387078803))) (le8 (Z_to_bv 64 2635249153387078803))])
      by (apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]).
    exact (ro_cells_read_at usegs m1 _ _ 0 _ 8 _ RC eq_refl eq_refl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Definition FAW (b0 b1 b2 b3 : Z) : list word :=
    let l1 := jt_len src 0 in let l2 := jt_len src 2 in let l3 := jt_len src 4 in
    let seg := (dcap + 3) / 4 in
    [ Z_to_bv 64 (SS + 6 + l1 - 8); Z_to_bv 64 (SS + 6 + l1 + l2 - 8); Z_to_bv 64 (SS + 6 + l1 + l2 + l3 - 8);
      Z_to_bv 64 (SS + n - 8);
      Z_to_bv 64 DST; Z_to_bv 64 (DST + seg); Z_to_bv 64 (DST + 2 * seg); Z_to_bv 64 (DST + 3 * seg);
      Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3;
      Z_to_bv 64 (DT + 4); Z_to_bv 64 SS; Z_to_bv 64 (DST + dcap);
      Z_to_bv 64 (SS + 6); Z_to_bv 64 (SS + 6 + l1); Z_to_bv 64 (SS + 6 + l1 + l2); Z_to_bv 64 (SS + 6 + l1 + l2 + l3) ].

  (* [comment removed for export] *)
  Lemma x4_stk4 : forall mm cs j1 j2, stk usegs mm lo (SP + -512) -> rw_cells usegs mm (SP + -512) cs ->
    cells_size cs = 136%nat -> rw_cells usegs mm (SP + -376) [CB 152 j1] -> rw_cells usegs mm (SP + -224) [CB 120 j2] ->
    stk usegs mm lo (SP + -104).
Proof using All.
    intros mm cs j1 j2 ST C L W1 W2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    release_frame C ST (SP + -376).
    release_frame W1 ST (SP + -224).
    release_frame W2 ST (SP + -104).
    exact ST.
  Qed.

  Lemma x4e_cb8 : forall m A pre b post, rw_cells usegs m A (pre ++ CB 8 b :: post) ->
    exists v, rw_cells usegs m A (pre ++ C8 v :: post).
  Proof.
    intros m A pre b post H. exists (le_bytes_to_word b).
    apply rw_cells_cb8_c8; [exact H|].
    destruct H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [_ [WB _]]. exact WB.
  Qed.

  Ltac x4e_c8l cs := lazymatch cs with
    | [] => constr:(@nil word)
    | C8 ?w :: ?r => let l := x4e_c8l r in constr:(w :: l)
    end.
  Ltac x4e_u64 H := lazymatch type of H with rw_cells ?sg ?m ?A ?cs =>
    let l := x4e_c8l cs in apply (u64arr_of_C8 sg m A l) in H end.
  Ltac x4e_cb8p cs := lazymatch cs with
    | CB 8 ?b :: ?post => constr:((@nil cell, b, post))
    | ?c :: ?r => let t := x4e_cb8p r in lazymatch t with (?p, ?b, ?q) => constr:((c :: p, b, q)) end
    end.
  Ltac x4e_cb8t H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let t := x4e_cb8p cs in lazymatch t with (?pre, ?b, ?post) =>
      let v := fresh "jv" in let H2 := fresh "H" in
      destruct (x4e_cb8 m A pre b post H) as [v H2]; clear H; rename H2 into H; cbn [app] in H end end.
  Ltac x4e_stk := match goal with
    | ST : stk _ ?m lo (SP + -512), C : rw_cells _ ?m (SP + -512) _, W1 : rw_cells _ ?m (SP + -376) [CB 152 _],
      W2 : rw_cells _ ?m (SP + -224) [CB 120 _] |- _ =>
        let S := fresh "STK" in pose proof (x4_stk4 _ _ _ _ ST C eq_refl W1 W2) as S end.
  Ltac x4e_slow :=
    eapply SLOW; split; [eexists; split; eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; eassumption.
  Ltac x4e_pack :=
    split; [eexists; split; eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eexists; eassumption|];
    split; [eassumption|]; split; [reflexivity|];
    split; [eassumption|]; split; [reflexivity|];
    split; [eassumption|]; split; [reflexivity|];
    split; [eassumption|]; split; [eassumption|]; split; eassumption.

  (* [comment removed for export] *)
  Lemma x4_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (flags : Z) (buf : list Z),
    u8arr usegs m0 DST (map (Z_to_bv 8) buf) -> zlen buf = dcap ->
    bytes_at usegs m0 SS (map (Z_to_bv 8) src) -> bytes_at usegs m0 (DT + 4) cbs ->
    bytes_at usegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl] ->
    stk usegs m0 lo SP -> mem_inv usegs m0 -> 0 <= flags < 64 ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                           (Z_to_bv 64 DT) (Z_to_bv 64 flags) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 PHUF_DX1_4X) fc None m0 (seg_rom usegs)).
Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 flags buf OUT LB SRCB CBSB DTB ST MI FL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl DW m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    carve_frame 104%nat ST. rename FR into FRa.
    carve_frame 120%nat ST. rename FR into FRf.
    carve_frame 152%nat ST. rename FR into FRw.
    carve_frame 136%nat ST. rename FR into FRs.
    unfold PHUF_DX1_4X.
    x4e_to 4000.
    if_cases K; zify_cond K.
    - pose proof (x4_stk4 _ _ _ _ ST FRs eq_refl FRw FRf) as STK.
      eapply SLOW.
      refine (conj _ (conj SRCB (conj CBSB (conj DTB (conj STK (conj FRa (conj MI (conj MU WM)))))))).
      exists buf; split; assumption.
    - pose proof (proj1 TOK) as TLB. try unfold HUF_TABLELOG_MAX in TLB.
      assert (LSRC : zlen (map (Z_to_bv 8) src) = n) by (f_equal; apply length_map).
      x4e_walk 29464.
      all: lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fast_args_proof with (A := SP + -376) (DST := DST) (dcap := dcap) (S := SS) (DT := DT)
            (mtl := mtl) (tt := 0) (tl := tl) (mtl' := mtl) (src := src) (ja := junk1) (lo := lo);
          rewrite ?unsigned_lit by lia;
          first [ assumption | reflexivity | lia | (f_equal; lia) | (apply bv_eq; rewrite !unsigned_lit by lia; lia) ]
        | intros ms' PO; unfold fast_args_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO; post_call segs m ] end.
      all: match goal with H : exists ja, rw_cells _ _ (SP + -376) [CB 152 ja] |- _ => destruct H as [jw FRw] end.
      all: match goal with H : ?r = 0 \/ _ |- _ => destruct H as [RV | [RV | [RV FOK]]] end.
      all: lazymatch type of RV with
        | ?r = 0 => subst r; x4e_walk 2544; x4e_stk; x4e_slow
        | ?r = 2^64 - 20 => subst r; x4e_walk 5120; x4e_stk; eapply x4e_epi; eassumption
        | ?r = 1 => subst r
        end.
      all: destruct FOK as (TL11 & N10 & J0 & J2 & J4 & JS & DCP & SEG3 & b0 & b1 & b2 & b3 & B0 & B1 & B2 & B3
                            & M0 & M1 & M2 & M3 & FAC).
      all: unfold fast_args_cells in FAC; cbv zeta in FAC.
      all: try (exfalso; repeat (match goal with H : context [bv_signed (Z_to_bv 64 _)] |- _ =>
                  rewrite signed_lit in H by lia end); lia).
      all: match goal with H : mem_inv _ ?m |- _ => pose proof (m7_rd _ H) as M7 end.
      all: x4e_walk 5252.
      all: match goal with |- context [Z_to_bv 64 (Z.lxor (DT + 4) ?M)] =>
        replace (Z_to_bv 64 (Z.lxor (DT + 4) M)) with (Z_to_bv 64 (- (DT + 4) - 1))
          by (rewrite zb_lxor_ones by lia; rewrite <- (Z_to_bv_mod64 (- (DT + 4) - 1)); f_equal;
              symmetry; apply Z.mod_unique_pos with (-1); lia) end.
      all: apply (proj1 (rw_cells_app' usegs _ _ [_] _)) in FRs; destruct FRs as [JK SPSc];
           cbn [cells_size csize Nat.add] in SPSc;
           replace (SP + -512 + Z.of_nat 56) with (SP + -456) in SPSc by lia.
      all: x4e_u64 SPSc. all: x4e_u64 FAC.
      all: x4e_cb8t FRf. all: x4e_cb8t FRf. all: x4e_cb8t FRf.
      all: x4e_u64 FRf.
      all: eapply (x4_outer ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs)
             with (fuel := Z.to_nat (dcap + 1)).
      all: try (unfold X4M; x4e_pack).
      all: try (lazymatch goal with |- nth_error _ 0%nat = _ /\ _ =>
                 solve [ repeat split; first [ reflexivity | rewrite unsigned_lit by lia; assumption ] ] end).
      all: try (lazymatch goal with |- forall i, 0 <= i < 4 -> _ =>
                 intros i Hi; assert (HI : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia;
                 destruct HI as [ -> | [ -> | [ -> | -> ] ] ];
                 (eexists; split; [ reflexivity | rewrite unsigned_lit by lia; lia ]) end).
      all: try (lazymatch goal with |- nth_error _ 13%nat = _ => reflexivity end).
      all: try assumption.
      all: try (rewrite <- TL11; exact TOK).
      all: try (rewrite ECB, TL11; reflexivity).
      all: try (rewrite LCB, TL11; reflexivity).
      all: try (apply DP; lia).
      all: try (rewrite TL11 in CBL; exact CBL).
      all: try (rewrite TL11 in DJ1; exact DJ1).
      all: try (Z.div_mod_to_equations; lia).
      all: try (rewrite Z2Nat.id by lia; lia).
      all: lia.
  Qed.

End X4E.
End CANSEC1.
