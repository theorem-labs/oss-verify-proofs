(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC SegLin.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInv SjS1Lem SjS1Bytes SjS1Ghost SjVCPre SjS1VC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Atoms.
Variable E : env.
Local Notation u := bv_unsigned.

Lemma ue_ext1 : forall x, u (edenot E (EExt false 0 1 x)) = u (edenot E x) mod 256.
Proof. intros x. cbn [edenot]. apply u_ext1. Qed.
Lemma ue_and : forall x k, 0 <= k < 2^64 -> u (edenot E (EAlu ALU_AND x (ELit k))) = Z.land (u (edenot E x)) k.
Proof. intros x k Hk. cbn [edenot]. rewrite u_and, ul by exact Hk. reflexivity. Qed.
Lemma ue_srl : forall x k, 0 <= k < 64 -> u (edenot E (EAlu ALU_SRL x (ELit k))) = u (edenot E x) / 2^k.
Proof.
  intros x k Hk. cbn [edenot]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small k) by lia. rewrite (Z.mod_small 63) by lia.
  replace (Z.land k 63) with k.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ue_sltu : forall x y, u (edenot E (EAlu ALU_SLTU x y)) = if u (edenot E x) <? u (edenot E y) then 1 else 0.
Proof. intros x y. cbn [edenot]. unfold alu64, alu, bv_ltu. destruct (_ <? _); reflexivity. Qed.
Lemma ue_xor_sltu1 : forall x y, u (edenot E (EAlu ALU_XOR (EAlu ALU_SLTU x y) (ELit 1))) = if u (edenot E x) <? u (edenot E y) then 0 else 1.
Proof.
  intros x y. cbn [edenot]. unfold alu64, alu, bv_ltu. rewrite bv_xor_unsigned.
  destruct (_ <? _); reflexivity.
Qed.
Lemma ue_lit : forall z, u (edenot E (ELit z)) = u (Z_to_bv 64 z).
Proof. reflexivity. Qed.
Lemma se_lit : forall z, bv_signed (edenot E (ELit z)) = bv_signed (Z_to_bv 64 z).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma se_sh56 : forall x, bv_signed (edenot E (EMd M_MUL (ELit 72057594037927936) (EExt false 0 1 x))) < 0 <-> 128 <= u (edenot E x) mod 256.
Proof.
  intros x. cbn [edenot].
  pose proof (sh56_sign (u (edenot E x) mod 256) ltac:(apply Z.mod_pos_bound; lia)) as S.
  replace (mul_div M_MUL (Z_to_bv 64 72057594037927936) (ext_val false 0 1 (edenot E x)))
    with (Z_to_bv 64 (72057594037927936 * (u (edenot E x) mod 256))); [exact S|].
  apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, u_ext1, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small 72057594037927936) by lia. reflexivity.
Qed.
End Atoms.

(* [comment removed for export] *)
Lemma ub_byte : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 64 b) = b.
Proof. intros b Hb. apply ul. lia. Qed.
Lemma ub_ctab : forall c, bv_unsigned (Z_to_bv 64 (ctab c)) = ctab c.
Proof. intros c. apply ul. pose proof (ctab_range c). lia. Qed.
Lemma ctab_mod256 : forall c, ctab c mod 256 = ctab c.
Proof. intros c. apply Z.mod_small. pose proof (ctab_range c). lia. Qed.
Lemma swrap8_cases : forall b, 0 <= b < 256 -> (b < 128 /\ bv_swrap 8 b = b) \/ (128 <= b /\ bv_swrap 8 b = b - 256).
Proof.
  intros b Hb. change (bv_swrap 8 b) with ((b + 128) mod 256 - 128). destruct (Z_lt_ge_dec b 128) as [L|G].
  - left. split; [exact L|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace (b + 128) with ((b - 128) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma usw_mod256 : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 64 (bv_swrap 8 b)) mod 256 = b.
Proof.
  intros b Hb. rewrite SV.u_lit. rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists (2^56); reflexivity).
  destruct (swrap8_cases b Hb) as [[_ ->]|[_ ->]]; [apply Z.mod_small; lia|].
  replace (b - 256) with (b + (-1) * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma usw_land255 : forall b, 0 <= b < 256 -> Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 8 b))) 255 = b.
Proof. intros b Hb. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply usw_mod256. exact Hb. Qed.
Lemma ssw : forall b, 0 <= b < 256 -> bv_signed (Z_to_bv 64 (bv_swrap 8 b)) = bv_swrap 8 b.
Proof. intros b Hb. apply sl. destruct (swrap8_cases b Hb) as [[_ ->]|[_ ->]]; lia. Qed.
Lemma is_cont_swrap : forall b, 0 <= b < 256 -> is_cont b = (bv_swrap 8 b <? -64).
Proof.
  assert (F : forallb (fun k => Bool.eqb (is_cont (Z.of_nat k)) (bv_swrap 8 (Z.of_nat k) <? -64)) (seq 0 256) = true) by (vm_compute; reflexivity).
  intros b Hb. rewrite forallb_forall in F. specialize (F (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in F by lia.
  apply Bool.eqb_prop in F. exact F.
Qed.

(* [comment removed for export] *)
Definition extb (sx : bool) (b : Z) : Z := if sx then bv_swrap 8 b else b.

Section Reads.
Variable segs : list Segment.
Variable d : list Z.
Variable E : env.
Variable m : word -> option byte.
Notation len := (zlength d).

Lemma rr_buf_lin : forall kn a sx v eb lenw l,
  know_ok segs E m kn -> lin_nowrap kn (EAlu ALU_ADD (a_base a) (ELit (a_off a))) = true -> lin_nowrap kn eb = true ->
  VP.lsubx (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) (lin_of eb) = l ->
  g_buf d m (edenot E eb) lenw -> sc_denot segs m E (SCReadBase a 1 sx (EVar v)) ->
  0 <= VP.pden E l < len + 64 -> ev E v = Z_to_bv 64 (extb sx (byte_at d (VP.pden E l))).
Proof.
  intros kn a sx v eb lenw l HK HN HNb HLl GB HR Hi. cbn [sc_denot] in HR. subst l.
  assert (A : bv_unsigned (adenot E a) = bv_unsigned (edenot E eb)
             + VP.pden E (VP.lsubx (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) (lin_of eb))).
  { rewrite (VP.u_adenot_lin segs E m kn a HK HN), (VP.u_lin segs E m kn eb HK HNb). rewrite !VP.pden_ok, VP.ld_sub. lia. }
  destruct sx.
  - exact (rr_buf_s segs d m _ lenw _ _ _ GB HR A Hi).
  - exact (rr_buf segs d m _ lenw _ _ _ GB HR A Hi).
Qed.

Lemma rr_tab_lin : forall kn a v es l,
  know_ok segs E m kn -> lin_nowrap kn (EAlu ALU_ADD (a_base a) (ELit (a_off a))) = true -> lin_nowrap kn es = true ->
  VP.laddc (VP.lsubx (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) (lin_of es)) 400 = l ->
  g_tab m (edenot E es) -> sc_denot segs m E (SCReadBase a 1 false (EVar v)) ->
  0 <= VP.pden E l < 256 -> ev E v = Z_to_bv 64 (ctab (VP.pden E l)).
Proof.
  intros kn a v es l HK HN HNs HLl GT HR Hc. cbn [sc_denot] in HR. subst l.
  assert (A : bv_unsigned (adenot E a) = bv_unsigned (edenot E es) - 400
             + VP.pden E (VP.laddc (VP.lsubx (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) (lin_of es)) 400)).
  { rewrite (VP.u_adenot_lin segs E m kn a HK HN), (VP.u_lin segs E m kn es HK HNs). rewrite !VP.pden_ok, VP.ld_addc, VP.ld_sub. lia. }
  exact (rr_tab segs m _ _ _ _ GT HR A Hc).
Qed.

(* [comment removed for export] *)
Lemma kword_keep : forall kn lg a w v, know_ok segs E m kn -> SLin.kin (KWord a w v) kn = true -> log_flat E lg ->
  (forall i, 0 <= i < Z.of_nat w -> SV.outside_log E lg (estart E a + i)) -> kentry_ok segs E (mem_denot E m lg) (KWord a w v).
Proof.
  intros kn lg a w v HK HI HL HO. pose proof (SLin.kin_ok segs E m kn _ HK HI) as K. cbn [kentry_ok] in K |- *.
  destruct K as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd.
  pose proof (flat_u E _ _ Hfl) as Fu. destruct Hfl as (F1 & F2 & F3 & F4).
  apply rdn_ext; [lia|]. intros x Hx. apply SV.md_outside; [exact HL|].
  specialize (HO (bv_unsigned x - estart E a) ltac:(lia)). replace (estart E a + (bv_unsigned x - estart E a)) with (bv_unsigned x) in HO by lia.
  exact HO.
Qed.
End Reads.


Lemma u_addneg2 : forall E x p, Zpos p <= bv_unsigned (edenot E x) ->
  bv_unsigned (edenot E (EAlu ALU_ADD x (ELit (Zneg p)))) = bv_unsigned (edenot E x) - Zpos p.
Proof.
  intros E x p H. cbn [edenot]. rewrite SV.u_alu_add, SV.u_lit. pose proof (ur (edenot E x)) as U.
  replace ((Zneg p) mod 2^64) with (2^64 - Zpos p) by (rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia; rewrite Z.mod_small; lia).
  replace (bv_unsigned (edenot E x) + (2^64 - Zpos p)) with ((bv_unsigned (edenot E x) - Zpos p) + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Section Bnd.
Variable d : list Z.
Local Notation u := bv_unsigned.
Lemma gm_bnd : forall M a1 j dd er, g_main d M a1 j dd er -> u a1 + u dd < 2^64.
Proof. intros M a1 j dd er (acc & H1 & H2 & _). exact H2. Qed.
Lemma gs_bnd : forall M a1 i k dd er, g_str d M a1 i k dd er -> u a1 + u dd + 4 < 2^64.
Proof. intros M a1 i k dd er (acc & H1 & H2 & _). exact H2. Qed.
Lemma gp_bnd : forall M a1 i k dd er, g_prim d M a1 i k dd er -> u a1 + u dd + 4 < 2^64.
Proof. intros M a1 i k dd er (acc & H1 & H2 & _). exact H2. Qed.
Lemma gp0_bnd : forall M a1 i k dd er, g_prim0 d M a1 i k dd er -> u a1 + u dd + 4 < 2^64.
Proof. intros M a1 i k dd er (acc & H1 & H2 & _). exact H2. Qed.
End Bnd.
Lemma u_addneg : forall E x p, Zpos p < 2^63 -> bv_unsigned (edenot E (EAlu ALU_ADD x (ELit (Zneg p)))) + Zpos p < 2^64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD x (ELit (Zneg p)))) = bv_unsigned (edenot E x) - Zpos p.
Proof.
  intros E x p Hc H. cbn [edenot] in *. rewrite SV.u_alu_add, SV.u_lit in *. pose proof (ur (edenot E x)) as U.
  replace ((Zneg p) mod 2^64) with (2^64 - Zpos p) in * by (rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia; rewrite Z.mod_small; lia).
  destruct (Z_lt_le_dec (bv_unsigned (edenot E x)) (Zpos p)) as [L|G].
  - rewrite Z.mod_small in H by lia. lia.
  - replace (bv_unsigned (edenot E x) + (2^64 - Zpos p)) with ((bv_unsigned (edenot E x) - Zpos p) + 1 * 2^64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.


(* [comment removed for export] *)
Lemma mbytes_app_r : forall M a bs1 bs2, mbytes M a (bs1 ++ bs2) -> mbytes M (a + Z.of_nat (length bs1)) bs2.
Proof.
  intros M a bs1 bs2 H i Hi. specialize (H (Z.of_nat (length bs1) + i) ltac:(rewrite length_app; lia)).
  replace (a + Z.of_nat (length bs1) + i) with (a + (Z.of_nat (length bs1) + i)) by lia. rewrite H.
  rewrite app_nth2 by lia. f_equal. f_equal. lia.
Qed.
Section Cell.
Variable d : list Z.
Local Notation u := bv_unsigned.
Lemma cell_of_rev : forall M (a1 i : word) acc, mbytes M (u a1) (u32bytes (rev (u i :: acc))) ->
  mbytes M (u a1 + 4 * zlength acc) (word_to_le_bytes 4 i).
Proof.
  intros M a1 i acc H. rewrite u32bytes_rev_cons in H. apply mbytes_app_r in H. rewrite u32bytes_len, zlength_rev' in H.
  rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Lemma gs_cell : forall M a1 i k dd er, g_str d M a1 i k dd er -> mbytes M (u a1 + u dd) (word_to_le_bytes 4 i).
Proof. intros M a1 i k dd er (acc & H1 & H2 & H3 & _). rewrite <- H1. exact (cell_of_rev M a1 i acc H3). Qed.
Lemma gp_cell : forall M a1 i k dd er, g_prim d M a1 i k dd er -> mbytes M (u a1 + u dd) (word_to_le_bytes 4 i).
Proof. intros M a1 i k dd er (acc & H1 & H2 & H3 & _). rewrite <- H1. exact (cell_of_rev M a1 i acc H3). Qed.
Lemma gp0_cell : forall M a1 i k dd er, g_prim0 d M a1 i k dd er -> mbytes M (u a1 + u dd) (word_to_le_bytes 4 i).
Proof. intros M a1 i k dd er (acc & H1 & H2 & H3 & _). rewrite <- H1. exact (cell_of_rev M a1 i acc H3). Qed.
End Cell.

Lemma rdn_mbytes : forall segs M bs (a : word), mbytes M (bv_unsigned a) bs -> bv_unsigned a + Z.of_nat (length bs) < 2^64 ->
  rdn segs M a (length bs) = Some bs.
Proof.
  intros segs M bs. induction bs as [|b bs IH]; intros a H HB; [reflexivity|].
  cbn [length] in HB. rewrite Nat2Z.inj_succ in HB.
  cbn [length rdn]. assert (H0 : M a = Some b).
  { specialize (H 0 ltac:(cbn [length]; lia)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. exact H. }
  assert (U : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
  rewrite H0. rewrite IH; [reflexivity| |].
  - intros i Hi. rewrite U. specialize (H (i + 1) ltac:(cbn [length]; rewrite Nat2Z.inj_succ; lia)).
    replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (i + 1)) by lia.
    rewrite H. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
  - rewrite U. lia.
Qed.

Lemma kword_of_cell : forall segs E M lg a v A, log_flat E lg -> mbytes M A (word_to_le_bytes 4 (edenot E v)) ->
  (forall i, 0 <= i < 4 -> SV.outside_log E lg (A + i)) -> bv_unsigned (adenot E a) = A -> flat E a 4 -> A + 4 < 2^64 ->
  kentry_ok segs E (mem_denot E M lg) (KWord a 4 v).
Proof.
  intros segs E M lg a v A HL HM HO HA Hfl HA4. cbn [kentry_ok]. split; [lia|]. split; [exact Hfl|].
  pose proof (flat_u E _ _ Hfl) as Fu. destruct Hfl as (F1 & F2 & F3 & F4).
  change 4%nat with (length (word_to_le_bytes 4 (edenot E v))) at 1.
  apply rdn_mbytes; [| rewrite le4_len; lia].  (* [comment removed for export] *)
  rewrite HA. intros i Hi. rewrite le4_len in Hi. rewrite SV.md_outside; [exact (HM i Hi)| exact HL|].
  rewrite ul by lia. exact (HO i Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlit z := lazymatch z with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end.
Ltac s1p_pow := repeat match goal with
  | |- context [2 ^ ?k] => zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v
  | H : context [2 ^ ?k] |- _ => zlit k; let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v in H
  end.

Ltac s1p_pden := cbn [VP.pden VP.psum VP.pterm VP.lsubx VP.laddc VP.laddx SLin.zadd_ts SLin.zscale_ts SLin.zins fold_right map
                       lin_of ladd lscale lscale_terms lins snorm fst snd Z.eqb Pos.eqb expr_eqb Nat.eqb Z.mul Z.add Z.opp Pos.mul Pos.add
                       Z.pos_sub Z.double Z.succ_double Z.pred_double Z.leb Z.ltb Z.compare Pos.compare Pos.compare_cont andb orb
                       Z.land Pos.land negb] in *;
                 unfold uE in *; rewrite ?VP.edenot_EVar in *.

(* [comment removed for export] *)
Ltac s1p_lin_hyps :=
  repeat match goal with
  | HK : know_ok ?segs ?E ?m ?kn, H : context [bv_unsigned (edenot ?E ?e)] |- _ =>
      lazymatch e with EVar _ => fail | ELit _ => fail | _ => idtac end;
      let l := eval vm_compute in (lin_of e) in
      rewrite (VP.u_lin' segs E m kn e l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) in H
  end; cbn [VP.pden VP.psum VP.pterm fst snd Z.eqb Pos.eqb] in *; unfold uE in *; rewrite ?VP.edenot_EVar in *.
(* [comment removed for export] *)
Ltac s1p_bnds :=
  try match goal with G : g_main ?d ?M ?a1 ?j ?dd ?er |- _ => let B := fresh "B" in pose proof (gm_bnd d M a1 j dd er G) as B end;
  try match goal with G : g_str ?d ?M ?a1 ?i ?k ?dd ?er |- _ => let B := fresh "B" in pose proof (gs_bnd d M a1 i k dd er G) as B end;
  try match goal with G : g_prim ?d ?M ?a1 ?i ?k ?dd ?er |- _ => let B := fresh "B" in pose proof (gp_bnd d M a1 i k dd er G) as B end;
  try match goal with G : g_prim0 ?d ?M ?a1 ?i ?k ?dd ?er |- _ => let B := fresh "B" in pose proof (gp0_bnd d M a1 i k dd er G) as B end;
  s1p_lin_hyps;
  repeat match goal with
  | H : context [edenot ?E (EAlu ALU_ADD ?x (ELit (Zneg ?p)))] |- _ =>
      lazymatch goal with _ : bv_unsigned (edenot E (EAlu ALU_ADD x (ELit (Zneg p)))) = _ |- _ => fail | _ => idtac end;
      let UN := fresh "UN" in
      assert (UN : bv_unsigned (edenot E (EAlu ALU_ADD x (ELit (Zneg p)))) = bv_unsigned (edenot E x) - Zpos p)
        by (first [apply (u_addneg E x p); lia | apply (u_addneg2 E x p); rewrite ?VP.edenot_EVar; lia]);
      rewrite ?VP.edenot_EVar in UN;
      pose proof (ur (edenot E (EAlu ALU_ADD x (ELit (Zneg p)))))
  end.

(* [comment removed for export] *)
Ltac s1p_intro :=
  unfold SG.vc_holds; cbn [SG.vc_kn SG.vc_path SG.vc_log SG.vc_src SG.vc_tgt SG.vc_facts];
  let E := fresh "E" in let m := fresh "m" in let HK := fresh "HK" in let HP := fresh "HP" in let HL := fresh "HL" in
  let HS := fresh "HS" in
  intros E m HK HP HL HS;
  let KN := fresh "KN" in lazymatch type of HK with know_ok _ _ _ ?kn => set (KN := kn) in HK end;
  let LG := fresh "LG" in lazymatch type of HL with log_flat _ ?lg => set (LG := lg) in HL |- * end;
  lazymatch type of HK with know_ok ?segs _ _ _ => VP.vp_digest segs E m HK HP end;
  unfold SG.gholds in HS;
  repeat match type of HS with
  | Forall _ (_ :: _) => apply Forall_cons_iff in HS; let X := fresh "G" in destruct HS as [X HS]
  | Forall _ [] => clear HS
  end;
  cbn [ST.g_id ST.g_args map s1_gp] in *; rewrite ?VP.edenot_EVar in *;
  try match goal with
  | H : g_buf _ _ _ _ |- _ =>
      let GL := fresh "GL" in let G20 := fresh "G20" in let GBB := fresh "GBB" in let GDB := fresh "GDB" in let GMB := fresh "GMB" in
      pose proof H as (GL & G20 & GBB & GDB & GMB)
  end;
  s1p_lin_hyps.

(* [comment removed for export] *)
Ltac s1p_name_byte R d i :=
  lazymatch goal with
  | bn := byte_at d i |- _ => fold bn in R
  | _ => let bn := fresh "b" in set (bn := byte_at d i) in R;
         let BR := fresh "BR" in assert (BR : 0 <= bn < 256) by (apply byte_at_range; assumption)
  end.

(* [comment removed for export] *)
Ltac s1p_reads_buf :=
  repeat match goal with
  | GB : g_buf ?d ?m ?bw ?lw, HK : know_ok ?segs _ _ ?kn,
    P : sc_denot ?segs ?m ?E (SCReadBase ?a 1%nat ?sx (EVar ?v)) |- _ =>
      lazymatch a with context [EExt _ _ _ _] => fail | _ => idtac end;
      let eb := lazymatch bw with ev _ ?n => constr:(EVar n) | edenot _ ?e => e end in
      let R := fresh "R_" in
      let l := eval vm_compute in (VP.lsubx (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) (lin_of eb)) in
      pose proof (rr_buf_lin segs d E m kn a sx v eb lw l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) GB P) as R;
      clear P; cbn [VP.pden VP.psum VP.pterm fst snd Z.eqb Pos.eqb] in R; unfold uE in R; rewrite ?VP.edenot_EVar in R;
      lazymatch type of R with
      | ?side -> _ => let S := fresh in assert (S : side) by lia; specialize (R S); clear S
      end;
      cbn [extb] in R;
      lazymatch type of R with ev _ _ = Z_to_bv 64 (bv_swrap 8 (byte_at ?d ?i)) => s1p_name_byte R d i
                              | ev _ _ = Z_to_bv 64 (byte_at ?d ?i) => s1p_name_byte R d i end
  end.

(* [comment removed for export] *)
Ltac s1p_atoms :=
  repeat match goal with
  | H : context [bv_unsigned (edenot ?E (EExt false 0 1 ?x))] |- _ => rewrite (ue_ext1 E x) in H
  | H : context [bv_unsigned (edenot ?E (EAlu ALU_XOR (EAlu ALU_SLTU ?x ?y) (ELit 1)))] |- _ => rewrite (ue_xor_sltu1 E x y) in H
  | H : context [bv_unsigned (edenot ?E (EAlu ALU_SLTU ?x ?y))] |- _ => rewrite (ue_sltu E x y) in H
  | H : context [bv_unsigned (edenot ?E (EAlu ALU_AND ?x (ELit ?k)))] |- _ => rewrite (ue_and E x k ltac:(lia)) in H
  | H : context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?x (ELit ?k)))] |- _ => rewrite (ue_srl E x k ltac:(lia)) in H
  | H : context [edenot ?E (EVar ?n)] |- _ => rewrite (VP.edenot_EVar E n) in H
  | H : context [bv_unsigned (edenot ?E (ELit ?z))] |- _ =>
      let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (edenot E (ELit z))) with v in H
  end.
Ltac s1p_subst :=
  repeat match goal with
  | R : ev ?E ?v = Z_to_bv 64 _, H : context [ev ?E ?v] |- _ => rewrite R in H
  end;
  repeat match goal with
  | BR : 0 <= ?b < 256 |- context [bv_unsigned (Z_to_bv 64 ?b)] => rewrite (ub_byte b BR)
  | BR : 0 <= ?b < 256, H : context [bv_unsigned (Z_to_bv 64 ?b)] |- _ => rewrite (ub_byte b BR) in H
  | BR : 0 <= ?b < 256, H : context [bv_unsigned (Z_to_bv 64 (bv_swrap 8 ?b)) mod 256] |- _ => rewrite (usw_mod256 b BR) in H
  | BR : 0 <= ?b < 256, H : context [Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 8 ?b))) 255] |- _ => rewrite (usw_land255 b BR) in H
  | BR : 0 <= ?b < 256, H : context [?b mod 256] |- _ => rewrite (Z.mod_small b 256 BR) in H
  | H : context [bv_unsigned (Z_to_bv 64 (ctab ?c))] |- _ => rewrite (ub_ctab c) in H
  | H : context [ctab ?c mod 256] |- _ => rewrite (ctab_mod256 c) in H
  end.

(* [comment removed for export] *)
Ltac s1p_reads_tab :=
  repeat match goal with
  | GT : g_tab ?m ?sw, HK : know_ok ?segs _ _ ?kn,
    P : sc_denot ?segs ?m ?E (SCReadBase ?a 1%nat false (EVar ?v)) |- _ =>
      lazymatch a with context [EExt _ _ _ _] => idtac end;
      let es := lazymatch sw with ev _ ?n => constr:(EVar n) | edenot _ ?e => e end in
      let R := fresh "R_" in
      let l := eval vm_compute in (VP.laddc (VP.lsubx (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) (lin_of es)) 400) in
      pose proof (rr_tab_lin segs E m kn a v es l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) GT P) as R;
      clear P; cbn [VP.pden VP.psum VP.pterm fst snd Z.eqb Pos.eqb] in R; unfold uE in R; rewrite ?VP.edenot_EVar in R;
      rewrite ?ue_ext1 in R; rewrite ?VP.edenot_EVar in R; s1p_subst;
      lazymatch type of R with
      | ?side -> _ => let S := fresh in assert (S : side) by lia; specialize (R S); clear S
      end;
      let CR := fresh "CR" in
      lazymatch type of R with ev _ _ = Z_to_bv 64 (ctab ?c) => pose proof (ctab_range c) as CR end
  end.

(* [comment removed for export] *)
Ltac s1p_signed :=
  repeat match goal with
  | H : sc_denot _ _ _ (SCBr _ _ _ _) |- _ => cbn [sc_denot] in H
  end;
  repeat match goal with
  | H : branch_taken BC_LT _ _ = true |- _ => apply bt_lt in H
  | H : branch_taken BC_LT _ _ = false |- _ => apply bt_nlt in H
  | H : branch_taken BC_GE _ _ = true |- _ => apply bt_ge in H
  | H : branch_taken BC_GE _ _ = false |- _ => apply bt_nge in H
  end;
  repeat match goal with
  | H : bv_signed (edenot ?E (EMd M_MUL (ELit 72057594037927936) (EExt false 0 1 ?x))) < bv_signed (edenot ?E (ELit 0)) |- _ =>
      rewrite se_lit in H; change (bv_signed (Z_to_bv 64 0)) with 0 in H; apply (proj1 (se_sh56 E x)) in H
  | H : bv_signed (edenot ?E (ELit 0)) <= bv_signed (edenot ?E (EMd M_MUL (ELit 72057594037927936) (EExt false 0 1 ?x))) |- _ =>
      rewrite se_lit in H; change (bv_signed (Z_to_bv 64 0)) with 0 in H;
      let G := fresh "Gs" in
      assert (bv_unsigned (edenot E x) mod 256 < 128) by (destruct (Z_lt_le_dec (bv_unsigned (edenot E x) mod 256) 128) as [?|G];
                                                  [assumption| apply (proj2 (se_sh56 E x)) in G; lia]); clear H
  | H : context [bv_signed (edenot ?E (ELit ?z))] |- _ =>
      rewrite (se_lit E z) in H; let v := eval vm_compute in (bv_signed (Z_to_bv 64 z)) in change (bv_signed (Z_to_bv 64 z)) with v in H
  end.

(* [comment removed for export] *)
Ltac zb_prop H :=
  first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.leb_le in H | apply Z.leb_gt in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H ].
Ltac s1p_ifs :=
  repeat match goal with
  | H : context [if ?c then _ else _] |- _ =>
      lazymatch type of H with _ = _ => idtac | _ <> _ => idtac | _ <= _ => idtac | _ < _ => idtac | _ <= _ <= _ => idtac end;
      lazymatch c with Z.ltb _ _ => idtac | Z.leb _ _ => idtac | Z.eqb _ _ => idtac end;
      let Hc := fresh "Hc" in destruct c eqn:Hc; cbv iota in H; zb_prop Hc; try (exfalso; lia)
  end.
(* [comment removed for export] *)
Ltac s1p_lits :=
  repeat match goal with
  | BR : 0 <= ?b < 256, H : ?b + ?c = 0 |- _ =>
      let v := eval vm_compute in (- c) in assert (b = v) by lia; clear H
  end.

(* [comment removed for export] *)
Ltac s1p_pre :=
  s1p_intro; s1p_signed; s1p_reads_buf; s1p_atoms; s1p_subst; s1p_reads_tab; s1p_subst;
  repeat match goal with
  | BR : 0 <= ?b < 256, H : context [bv_signed (Z_to_bv 64 (bv_swrap 8 ?b))] |- _ => rewrite (ssw b BR) in H
  end;
  repeat match goal with R : ev _ _ = Z_to_bv 64 _ |- _ => clear R end;
  s1p_pow; s1p_ifs; s1p_lits; s1p_bnds.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Exits.
Variable d : list Z.
Notation len := (zlength d).
Local Notation u := bv_unsigned.

Definition xmem (M : word -> option byte) (a1 n this : word) (l : list Z) : Prop :=
  u n = zlength l /\ u a1 + 4 * u n + 12 < 2^64 /\ mbytes M (u a1) (u32bytes (rev l ++ [len; len; 0]))
  /\ u this + 28 < 2^64 /\ mbytes M (u this + 24) (word_to_le_bytes 4 (Z_to_bv 64 0)).

Lemma gm_exit : forall M0 M a1 j dd er rc n this (f : list Z -> list Z) err' uncl',
  g_main d M0 a1 j dd er ->
  (forall acc, S1C d (u j) acc (errb er) = fin3 (f acc, err', uncl')) ->
  (forall acc, 4 * zlength acc = u dd -> (u rc = 0 <-> fst (fin3 (f acc, err', uncl')) = true)) ->
  (forall acc, 4 * zlength acc = u dd -> u a1 + u dd < 2^64 -> mbytes M0 (u a1) (u32bytes (rev acc)) -> u rc = 0 ->
     xmem M a1 n this (f acc)) ->
  g_exit d M a1 rc n this.
Proof.
  intros M0 M a1 j dd er rc n this f err' uncl' (acc & H1 & H2 & H3 & H4) HS HC HM.
  apply gx_intro with (acc := f acc) (err := err') (uncl := uncl').
  - rewrite H4. apply HS.
  - apply HC. exact H1.
  - intros H0. exact (HM acc H1 H2 H3 H0).
Qed.

Lemma gs_exit : forall M0 M a1 i k dd er rc n this (f : list Z -> list Z) err' uncl',
  g_str d M0 a1 i k dd er ->
  (forall acc, SRES d (u i) acc (VSC d (u k) (errb er)) = fin3 (f acc, err', uncl')) ->
  (forall acc, 4 * zlength acc = u dd -> (u rc = 0 <-> fst (fin3 (f acc, err', uncl')) = true)) ->
  (forall acc, 4 * zlength acc = u dd -> u a1 + u dd + 4 < 2^64 -> mbytes M0 (u a1) (u32bytes (rev (u i :: acc))) -> u rc = 0 ->
     xmem M a1 n this (f acc)) ->
  g_exit d M a1 rc n this.
Proof.
  intros M0 M a1 i k dd er rc n this f err' uncl' (acc & H1 & H2 & H3 & H4) HS HC HM.
  apply gx_intro with (acc := f acc) (err := err') (uncl := uncl').
  - rewrite H4. apply HS.
  - apply HC. exact H1.
  - intros H0. exact (HM acc H1 H2 H3 H0).
Qed.

Lemma gp_exit : forall M0 M a1 i k dd er rc n this (f : list Z -> list Z) err' uncl',
  g_prim d M0 a1 i k dd er ->
  (forall acc, u k + 1 < len -> primc (byte_at d (u k + 1)) = true ->
     S1C d (PEC d (u k) + 1) (u i :: acc) (errb er) = fin3 (f acc, err', uncl')) ->
  (forall acc, 4 * zlength acc = u dd -> (u rc = 0 <-> fst (fin3 (f acc, err', uncl')) = true)) ->
  (forall acc, 4 * zlength acc = u dd -> u a1 + u dd + 4 < 2^64 -> mbytes M0 (u a1) (u32bytes (rev (u i :: acc))) -> u rc = 0 ->
     xmem M a1 n this (f acc)) ->
  g_exit d M a1 rc n this.
Proof.
  intros M0 M a1 i k dd er rc n this f err' uncl' (acc & H1 & H2 & H3 & HK & HP & H4) HS HC HM.
  apply gx_intro with (acc := f acc) (err := err') (uncl := uncl').
  - rewrite H4. apply HS; assumption.
  - apply HC. exact H1.
  - intros H0. exact (HM acc H1 H2 H3 H0).
Qed.

(* [comment removed for export] *)
Lemma rc_fail : forall (rc : word) R, u rc <> 0 -> fst (fin3 R) = false -> (u rc = 0 <-> fst (fin3 R) = true).
Proof. intros rc R H1 H2. rewrite H2. split; [intros; contradiction| discriminate]. Qed.
Lemma rc_err : forall (er : word) l, l <> [] -> (u er = 0 <-> fst (fin3 (l, errb er, false)) = true).
Proof.
  intros er l Hl. cbn [fin3 fst]. destruct l as [|x l]; [contradiction|]. unfold errb. cbn [negb andb].
  destruct (u er =? 0) eqn:E; cbn; [apply Z.eqb_eq in E; tauto|]. apply Z.eqb_neq in E. split; [contradiction| discriminate].
Qed.
Lemma fin3_uncl : forall l e, fst (fin3 (l, e, true)) = false.
Proof. intros l e. cbn [fin3 fst]. rewrite andb_false_r. reflexivity. Qed.
Lemma fin3_empty : forall e u', fst (fin3 ([], e, u')) = false.
Proof. intros e u'. reflexivity. Qed.
End Exits.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cells.
Variable E : env.

Lemma mcell_head : forall M a w v rest A x, log_flat E (SE a w v :: rest) -> bv_unsigned (adenot E a) = A -> w = 4%nat ->
  edenot E v = Z_to_bv 64 x -> mbytes (mem_denot E M (SE a w v :: rest)) A (word_to_le_bytes 4 (Z_to_bv 64 x)).
Proof. intros M a w v rest A x HF HA -> HV. rewrite <- HV. apply mbytes_log_head; assumption. Qed.

Lemma mcell_skip : forall M a w v rest A bs, log_flat E (SE a w v :: rest) ->
  (A + Z.of_nat (length bs) <= estart E a \/ estart E a + Z.of_nat w <= A) -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  mbytes (mem_denot E M rest) A bs -> mbytes (mem_denot E M (SE a w v :: rest)) A bs.
Proof.
  intros M a w v rest A bs HF HO H0 H1 H. apply mbytes_log_skip; [exact HF| |exact H0|exact H1|exact H].
  intros i Hi. cbn [SV.outside_log]. split; [|exact I]. lia.
Qed.

Lemma log_flat_tl : forall e rest, log_flat E (e :: rest) -> log_flat E rest.
Proof. intros [a w v] rest H. cbn [log_flat] in H. tauto. Qed.

Lemma mbytes_u32_app : forall M A l1 l2, mbytes M A (u32bytes l1) -> mbytes M (A + 4 * zlength l1) (u32bytes l2) ->
  mbytes M A (u32bytes (l1 ++ l2)).
Proof. intros M A l1 l2 H1 H2. rewrite u32bytes_app. apply mbytes_app; [exact H1|]. rewrite u32bytes_len. exact H2. Qed.
Lemma mbytes_u32_cons : forall M A x l, mbytes M A (word_to_le_bytes 4 (Z_to_bv 64 x)) -> mbytes M (A + 4) (u32bytes l) ->
  mbytes M A (u32bytes (x :: l)).
Proof. intros M A x l H1 H2. cbn [u32bytes]. apply mbytes_app; [exact H1|]. rewrite le4_len. exact H2. Qed.
Lemma mbytes_nil : forall M A, mbytes M A (u32bytes []).
Proof. intros M A i Hi. cbn in Hi. lia. Qed.
End Cells.

(* [comment removed for export] *)
Lemma gp_same' : forall d M a1 i k k' dd er, g_prim d M a1 i k dd er -> bv_unsigned k' = bv_unsigned k + 1 ->
  bv_unsigned k' + 1 < zlength d -> primc (byte_at d (bv_unsigned k' + 1)) = true -> g_prim d M a1 i k' dd er.
Proof.
  intros d M a1 i k k' dd er GP HK' HK2 HP2. pose proof GP as (acc & H1 & H2 & H3 & HK & HP & H4).
  exact (gp_same d M a1 i k k' dd er GP HK HP HK' HK2 HP2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Prim0.
Variable d : list Z.
Notation len := (zlength d).
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma gm_to_prim0 : forall E M a1 j dd er (a : saddr) (v : expr) i k er',
  g_main d M a1 j dd er -> log_flat E [SE a 4 v] -> u (adenot E a) = u a1 + u dd -> u a1 + u dd + 4 < 2^64 ->
  u i = u (edenot E v) ->
  (forall acc, S1C d (u j) acc (errb er) = S1C d (PEC d (u k) + 1) (u i :: acc) (errb er')) ->
  g_prim0 d (mem_denot E M [SE a 4 v]) a1 i k dd er'.
Proof.
  intros E M a1 j dd er a v i k er' (acc & H1 & H2 & H3 & H4) HF HA HB HI HS.
  exists acc. split; [exact H1|]. split; [lia|]. split.
  - rewrite HI. apply gm_push_mem with (dd := u dd); [exact H3| lia| pose proof (ur a1); lia| lia| exact HF| exact HA].
  - rewrite H4. apply HS.
Qed.

(* [comment removed for export] *)
Lemma gp0_step : forall M M' a1 i k k' dd er,
  g_prim0 d M a1 i k dd er -> (forall l, mbytes M (u a1) l -> Z.of_nat (length l) = u dd + 4 -> mbytes M' (u a1) l) ->
  u k' = u k + 1 -> u k + 1 < len -> primc (byte_at d (u k + 1)) = true -> g_prim0 d M' a1 i k' dd er.
Proof.
  intros M M' a1 i k k' dd er (acc & H1 & H2 & H3 & H4) HM HK HL HP. exists acc.
  split; [exact H1|]. split; [exact H2|]. split.
  - apply HM; [exact H3|]. rewrite u32bytes_len, zlength_rev', zlength_cons. lia.
  - rewrite H4. f_equal. f_equal. rewrite HK. apply PEC_step; [pose proof (ur k); lia| exact HL| exact HP].
Qed.

(* [comment removed for export] *)
Lemma gp0_to_main : forall M M' a1 i k j' dd dd' er,
  g_prim0 d M a1 i k dd er -> (forall l, mbytes M (u a1) l -> Z.of_nat (length l) = u dd + 4 -> mbytes M' (u a1) l) ->
  (len <= u k + 1 \/ primc (byte_at d (u k + 1)) = false) -> u j' = u k + 1 -> u dd' = u dd + 4 -> g_main d M' a1 j' dd' er.
Proof.
  intros M M' a1 i k j' dd dd' er (acc & H1 & H2 & H3 & H4) HM HE HJ HD. exists (u i :: acc).
  split; [rewrite zlength_cons; lia|]. split; [lia|]. split.
  - apply HM; [exact H3|]. rewrite u32bytes_len, zlength_rev', zlength_cons. lia.
  - rewrite H4. f_equal. rewrite HJ. rewrite PEC_here by exact HE. reflexivity.
Qed.

Lemma gp0_exit : forall M0 M a1 i k dd er rc n this (f : list Z -> list Z) err' uncl',
  g_prim0 d M0 a1 i k dd er ->
  (forall acc, S1C d (PEC d (u k) + 1) (u i :: acc) (errb er) = fin3 (f acc, err', uncl')) ->
  (forall acc, 4 * zlength acc = u dd -> (u rc = 0 <-> fst (fin3 (f acc, err', uncl')) = true)) ->
  (forall acc, 4 * zlength acc = u dd -> u a1 + u dd + 4 < 2^64 -> mbytes M0 (u a1) (u32bytes (rev (u i :: acc))) -> u rc = 0 ->
     xmem d M a1 n this (f acc)) ->
  g_exit d M a1 rc n this.
Proof.
  intros M0 M a1 i k dd er rc n this f err' uncl' (acc & H1 & H2 & H3 & H4) HS HC HM.
  apply gx_intro with (acc := f acc) (err := err') (uncl := uncl').
  - rewrite H4. apply HS.
  - apply HC. exact H1.
  - intros H0. exact (HM acc H1 H2 H3 H0).
Qed.
End Prim0.

(* [comment removed for export] *)
Section Gen.
Variable d : list Z.
Notation len := (zlength d).
Local Notation u := bv_unsigned.
Definition keepw (M M' : word -> option byte) (a1 : word) (w : Z) : Prop :=
  forall l, mbytes M (u a1) l -> Z.of_nat (length l) = w -> mbytes M' (u a1) l.

Lemma keep_push : forall M M' a1 acc x, mbytes M (u a1) (u32bytes (rev acc)) -> keepw M M' a1 (4 * zlength acc) ->
  mbytes M' (u a1 + 4 * zlength acc) (word_to_le_bytes 4 (Z_to_bv 64 x)) -> mbytes M' (u a1) (u32bytes (rev (x :: acc))).
Proof.
  intros M M' a1 acc x H HK HC. rewrite u32bytes_rev_cons. apply mbytes_app.
  - apply HK; [exact H|]. rewrite u32bytes_len, zlength_rev'. reflexivity.
  - rewrite u32bytes_len, zlength_rev'. exact HC.
Qed.

Lemma gm_same_gen : forall M M' a1 j j' dd er er',
  g_main d M a1 j dd er -> (forall acc, S1C d (u j) acc (errb er) = S1C d (u j') acc (errb er')) -> keepw M M' a1 (u dd) ->
  g_main d M' a1 j' dd er'.
Proof.
  intros M M' a1 j j' dd er er' (acc & H1 & H2 & H3 & H4) HS HK. exists acc. split; [exact H1|]. split; [exact H2|]. split.
  - apply HK; [exact H3|]. rewrite u32bytes_len, zlength_rev'. lia.
  - rewrite H4. apply HS.
Qed.

Lemma gm_push_gen : forall M M' a1 j j' dd dd' er er' x,
  g_main d M a1 j dd er -> (forall acc, S1C d (u j) acc (errb er) = S1C d (u j') (x :: acc) (errb er')) ->
  u a1 + u dd + 4 < 2^64 -> u dd' = u dd + 4 ->
  keepw M M' a1 (u dd) -> mbytes M' (u a1 + u dd) (word_to_le_bytes 4 (Z_to_bv 64 x)) -> g_main d M' a1 j' dd' er'.
Proof.
  intros M M' a1 j j' dd dd' er er' x (acc & H1 & H2 & H3 & H4) HS HB HD HK HC. exists (x :: acc).
  split; [rewrite zlength_cons; lia|]. split; [lia|]. split.
  - apply (keep_push M M' a1 acc); [exact H3| rewrite H1; exact HK| rewrite H1; exact HC].
  - rewrite H4. apply HS.
Qed.

Lemma gm_to_str_gen : forall M M' a1 j dd er i k er',
  g_main d M a1 j dd er -> (forall acc, S1C d (u j) acc (errb er) = SRES d (u i) acc (VSC d (u k) (errb er'))) ->
  u a1 + u dd + 4 < 2^64 ->
  keepw M M' a1 (u dd) -> mbytes M' (u a1 + u dd) (word_to_le_bytes 4 (Z_to_bv 64 (u i))) -> g_str d M' a1 i k dd er'.
Proof.
  intros M M' a1 j dd er i k er' (acc & H1 & H2 & H3 & H4) HS HB HK HC. exists acc.
  split; [exact H1|]. split; [lia|]. split.
  - apply (keep_push M M' a1 acc); [exact H3| rewrite H1; exact HK| rewrite H1; exact HC].
  - rewrite H4. apply HS.
Qed.

Lemma gm_to_prim_gen : forall M M' a1 j dd er i k er',
  g_main d M a1 j dd er -> (forall acc, S1C d (u j) acc (errb er) = S1C d (PEC d (u k) + 1) (u i :: acc) (errb er')) ->
  u k + 1 < len -> primc (byte_at d (u k + 1)) = true -> u a1 + u dd + 4 < 2^64 ->
  keepw M M' a1 (u dd) -> mbytes M' (u a1 + u dd) (word_to_le_bytes 4 (Z_to_bv 64 (u i))) -> g_prim d M' a1 i k dd er'.
Proof.
  intros M M' a1 j dd er i k er' (acc & H1 & H2 & H3 & H4) HS HK1 HP HB HK HC. exists acc.
  split; [exact H1|]. split; [lia|]. split.
  - apply (keep_push M M' a1 acc); [exact H3| rewrite H1; exact HK| rewrite H1; exact HC].
  - split; [exact HK1|]. split; [exact HP|]. rewrite H4. apply HS.
Qed.

Lemma gm_to_prim0_gen : forall M M' a1 j dd er i k er',
  g_main d M a1 j dd er -> (forall acc, S1C d (u j) acc (errb er) = S1C d (PEC d (u k) + 1) (u i :: acc) (errb er')) ->
  u a1 + u dd + 4 < 2^64 ->
  keepw M M' a1 (u dd) -> mbytes M' (u a1 + u dd) (word_to_le_bytes 4 (Z_to_bv 64 (u i))) -> g_prim0 d M' a1 i k dd er'.
Proof.
  intros M M' a1 j dd er i k er' (acc & H1 & H2 & H3 & H4) HS HB HK HC. exists acc.
  split; [exact H1|]. split; [lia|]. split.
  - apply (keep_push M M' a1 acc); [exact H3| rewrite H1; exact HK| rewrite H1; exact HC].
  - rewrite H4. apply HS.
Qed.

Lemma gp_same_gen : forall M M' a1 i k k' dd er,
  g_prim d M a1 i k dd er -> u k' = u k + 1 -> u k' + 1 < len -> primc (byte_at d (u k' + 1)) = true ->
  keepw M M' a1 (u dd + 4) -> g_prim d M' a1 i k' dd er.
Proof.
  intros M M' a1 i k k' dd er (acc & H1 & H2 & H3 & HK & HP & H4) HK' HK2 HP2 HM. exists acc.
  split; [exact H1|]. split; [exact H2|]. split.
  - apply HM; [exact H3|]. rewrite u32bytes_len, zlength_rev', zlength_cons. lia.
  - split; [exact HK2|]. split; [exact HP2|]. rewrite H4. f_equal. f_equal. rewrite HK'.
    apply PEC_step; [pose proof (ur k); lia| exact HK| exact HP].
Qed.

Lemma gp_to_main_gen : forall M M' a1 i k j' dd dd' er,
  g_prim d M a1 i k dd er -> (u k + 2 >= len \/ primc (byte_at d (u k + 2)) = false) ->
  u j' = u k + 2 -> u dd' = u dd + 4 -> keepw M M' a1 (u dd + 4) -> g_main d M' a1 j' dd' er.
Proof.
  intros M M' a1 i k j' dd dd' er (acc & H1 & H2 & H3 & HK & HP & H4) HE HJ HD HM. exists (u i :: acc).
  split; [rewrite zlength_cons; lia|]. split; [lia|]. split.
  - apply HM; [exact H3|]. rewrite u32bytes_len, zlength_rev', zlength_cons. lia.
  - rewrite H4. f_equal. rewrite HJ. rewrite PEC_step by (pose proof (ur k); lia || assumption).
    rewrite PEC_here; [lia|]. replace (u k + 1 + 1) with (u k + 2) by lia. destruct HE; [left; lia| right; assumption].
Qed.
End Gen.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac s1p_fold :=
  repeat match goal with
  | |- context [byte_at ?d (?x + ?a + ?b)] => zlit a; zlit b;
      let c := eval vm_compute in (a + b) in rewrite <- (Z.add_assoc x a b); change (a + b) with c
  end;
  repeat match goal with
  | bn := byte_at ?d ?i |- context [byte_at ?d ?i] => change (byte_at d i) with bn
  end;
  repeat match goal with
  | bn := byte_at ?d ?j |- context [byte_at ?d ?i] =>
      let E := fresh in assert (E : i = j) by lia; rewrite E; clear E; change (byte_at d j) with bn
  end.
Ltac s1p_fold_in H :=
  repeat match goal with
  | bn := byte_at ?d ?i |- _ => lazymatch type of H with context [byte_at d i] => change (byte_at d i) with bn in H end
  end.

(* [comment removed for export] *)
Ltac s1p_lin :=
  repeat match goal with
  | |- context [estart ?E ?a] => unfold estart; cbn [a_base a_off]
  | |- context [elenZ ?E ?n] => unfold elenZ
  | HK : know_ok ?segs ?E ?m ?kn |- context [bv_unsigned (adenot ?E ?a)] =>
      let l := eval vm_compute in (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))) in
      rewrite (VP.u_adenot_lin' segs E m kn a l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  | |- context [bv_unsigned (edenot ?E (EAlu ALU_SRL ?x (ELit ?k)))] => rewrite (ue_srl E x k ltac:(lia))
  | HK : know_ok ?segs ?E ?m ?kn |- context [bv_unsigned (edenot ?E ?e)] =>
      lazymatch e with EVar _ => fail | ELit _ => fail | EAlu ALU_SRL _ (ELit _) => fail | _ => idtac end;
      let l := eval vm_compute in (lin_of e) in
      rewrite (VP.u_lin' segs E m kn e l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  | |- context [bv_unsigned (edenot ?E (ELit ?z))] =>
      let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (edenot E (ELit z))) with v
  end;
  cbn [VP.pden VP.psum VP.pterm fst snd Z.eqb Pos.eqb];
  unfold uE; rewrite ?VP.edenot_EVar;
  repeat match goal with
  | UN : bv_unsigned (edenot ?E (EAlu ALU_ADD ?x (ELit (Zneg ?p)))) = _ |- context [bv_unsigned (edenot ?E (EAlu ALU_ADD ?x (ELit (Zneg ?p))))] =>
      rewrite UN
  end.
Ltac s1p_arith := s1p_lin; lia.
(* [comment removed for export] *)
Ltac s1p_alia :=
  first [ lia
        | match goal with H : VP.disj _ _ |- _ => let H' := fresh "D" in pose proof H as H'; unfold VP.disj in H'; lia end ].

(* [comment removed for export] *)
Ltac zb_lia_dec x y kind :=
  lazymatch kind with
  | 0 => first [ rewrite (proj2 (Z.eqb_neq x y)) by (first [assumption | lia]) | rewrite (proj2 (Z.eqb_eq x y)) by (first [assumption | lia]) ]
  | 1 => first [ rewrite (proj2 (Z.ltb_lt x y)) by (first [assumption | lia]) | rewrite (proj2 (Z.ltb_ge x y)) by (first [assumption | lia]) ]
  | 2 => first [ rewrite (proj2 (Z.leb_le x y)) by (first [assumption | lia]) | rewrite (proj2 (Z.leb_gt x y)) by (first [assumption | lia]) ]
  end.
(* [comment removed for export] *)
Ltac s1m_lit_bytes :=
  repeat match goal with
  | H : ?b = ?v |- context [?b] => match goal with bn := byte_at _ _ |- _ => constr_eq b bn end; rewrite H
  end.
Ltac s1m_batom :=
  match goal with
  | |- context [is_cont ?c] => rewrite (is_cont_swrap c ltac:(lia))
  | H : is_space ?c = ?v |- context [is_space ?c] => rewrite H
  | H : is_op ?c = ?v |- context [is_op ?c] => rewrite H
  | H : is_ascii_stop ?c = ?v |- context [is_ascii_stop ?c] => rewrite H
  | |- context [Z.eqb ?x ?y] => zb_lia_dec x y 0
  | |- context [Z.ltb ?x ?y] => zb_lia_dec x y 1
  | |- context [Z.leb ?x ?y] => zb_lia_dec x y 2
  end.
Ltac s1m_closed :=
  repeat match goal with
  | |- context [Z.land ?x ?y] => zlit x; zlit y; let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v
  | |- context [Z.eqb ?x ?y] => zlit x; zlit y; let v := eval vm_compute in (Z.eqb x y) in change (Z.eqb x y) with v
  | |- context [Z.ltb ?x ?y] => zlit x; zlit y; let v := eval vm_compute in (Z.ltb x y) in change (Z.ltb x y) with v
  | |- context [Z.leb ?x ?y] => zlit x; zlit y; let v := eval vm_compute in (Z.leb x y) in change (Z.leb x y) with v
  end; cbn [andb orb negb].
Ltac s1m_bdec := s1m_lit_bytes; s1m_closed;
  repeat (s1m_batom; cbn [andb orb negb]); rewrite ?andb_false_r, ?andb_true_r, ?orb_false_r, ?orb_true_r.
Ltac s1m_side := s1p_fold; first [assumption | lia | (unfold primc; s1m_bdec; reflexivity) | (right; unfold primc; s1m_bdec; reflexivity)].

(* [comment removed for export] *)
Ltac s1m_vsc d k e :=
  first [ rewrite (VSC_stop d k e) by s1m_side
        | rewrite (VSC_quote d k e) by s1m_side
        | rewrite (VSC_plain d k e) by s1m_side
        | rewrite (VSC_bslash d k e) by s1m_side
        | rewrite (VSC_ctrl d k e) by s1m_side
        | rewrite (VSC_utf8 d k e) by s1m_side; unfold utf8_char; cbv beta zeta; s1p_fold; s1m_bdec; cbv beta iota;
          rewrite ?orb_false_r, ?orb_true_r ].
Ltac s1m_pec d k :=
  first [ rewrite (PEC_here d k) by (first [left; lia | right; s1m_side])
        | rewrite (PEC_step d k) by s1m_side ].
Ltac s1m_step :=
  lazymatch goal with
  | |- S1C ?d ?j ?acc ?e = _ =>
      lazymatch j with
      | context [PEC ?d ?k] => s1m_pec d k
      | _ => first [ rewrite (S1C_stop d j acc e) by s1m_side
                   | rewrite (S1C_space d j acc e) by s1m_side
                   | rewrite (S1C_string d j acc e) by s1m_side
                   | rewrite (S1C_op d j acc e) by s1m_side
                   | rewrite (S1C_prim d j acc e) by s1m_side ]
      end
  | |- SRES ?d ?i ?acc (VSC ?d ?k ?e) = _ => s1m_vsc d k e
  | |- SRES ?d ?i ?acc (_, _) = _ => cbn [SRES]
  | |- VSC ?d ?k ?e = _ => s1m_vsc d k e
  end.
(* [comment removed for export] *)
Ltac s1m_run :=
  repeat (lazymatch goal with
          | |- ?x = ?x => fail
          | |- S1C _ ?j _ _ = S1C _ ?j _ _ => fail
          | |- VSC _ ?k _ = VSC _ ?k _ => fail
          | |- SRES _ _ _ (VSC _ ?k _) = SRES _ _ _ (VSC _ ?k _) => fail
          | _ => s1m_step end);
  first [ lazymatch goal with |- ?x = ?x => reflexivity end
        | (lazymatch goal with |- ?G => has_evar G end; reflexivity)
        | (f_equal; lia)
        | (f_equal; [f_equal; lia|]) ].

(* [comment removed for export] *)
Ltac s1p_facts :=
  unfold know_ok;
  repeat match goal with
  | |- Forall _ (_ :: _) => apply Forall_cons; [|]
  | |- Forall _ [] => apply Forall_nil
  end;
  try (lazymatch goal with
       | HK : know_ok ?segs ?E ?m ?kn, HL : log_flat ?E ?lg |- kentry_ok ?segs ?E (mem_denot ?E ?m ?lg) (KWord ?a ?w ?v) =>
           first
           [ apply (kword_keep segs E m kn lg a w v HK ltac:(vm_compute; reflexivity) HL);
             let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; cbn [SV.outside_log]; s1p_lin; repeat split; s1p_alia
           | let C := fresh "C" in
             first [ match goal with G : g_str ?d m ?a1 ?i0 ?k ?dd ?er |- _ => pose proof (gs_cell d m a1 i0 k dd er G) as C end
                   | match goal with G : g_prim ?d m ?a1 ?i0 ?k ?dd ?er |- _ => pose proof (gp_cell d m a1 i0 k dd er G) as C end
                   | match goal with G : g_prim0 ?d m ?a1 ?i0 ?k ?dd ?er |- _ => pose proof (gp0_cell d m a1 i0 k dd er G) as C end ];
             eapply (kword_of_cell segs E m lg a v); [exact HL| exact C| | | |];
             [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; cbn [SV.outside_log]; s1p_lin; repeat split; s1p_alia
             | s1p_arith
             | unfold flat, estart; cbn [a_base a_off]; s1p_lin; lia
             | s1p_lin; lia ] ]
       end).
Ltac s1p_tgt :=
  split; [|s1p_facts];
  unfold SG.gholds;
  repeat match goal with
  | |- Forall _ (_ :: _) => apply Forall_cons; [|]
  | |- Forall _ [] => apply Forall_nil
  end;
  cbn [ST.g_id ST.g_args map s1_gp]; rewrite ?VP.edenot_EVar.

(* [comment removed for export] *)
Ltac s1p_keep :=
  let l := fresh "l" in let Hm := fresh "Hm" in let Hl := fresh "Hl" in intros l Hm Hl; s1p_lin_hyps; s1p_lin;
  lazymatch goal with
  | |- mbytes (mem_denot _ _ []) _ _ => exact Hm
  | HL : log_flat ?E ?lg |- mbytes (mem_denot ?E _ ?lg) _ _ =>
      apply (mbytes_log_out E _ lg); [exact HL| lia | lia | | exact Hm];
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; cbn [SV.outside_log]; s1p_lin; repeat split; s1p_alia
  end.

(* [comment removed for export] *)
Ltac s1p_lflat := solve [repeat (first [eassumption | eapply log_flat_tl])].

(* [comment removed for export] *)
Ltac s1p_cell :=
  first
  [ eapply mcell_head; [s1p_lflat | s1p_arith | reflexivity | apply w_eq; s1p_lin; rewrite ?ul by lia; lia]
  | eapply mcell_skip; [s1p_lflat | rewrite ?le4_len; s1p_lin; s1p_alia | rewrite ?le4_len; s1p_arith | rewrite ?le4_len; s1p_arith | s1p_cell ] ].

(* [comment removed for export] *)
Ltac s1p_model := let acc := fresh "acc" in intros acc; s1p_lin; s1m_run.
Ltac s1p_kw := unfold keepw; s1p_keep.
Ltac s1p_edge :=
  lazymatch goal with
  (* [comment removed for export] *)
  | GM : g_main ?d ?M ?a1 ?j ?dd ?er |- g_main ?d _ _ _ _ _ =>
      first [ eapply gm_same_gen; [exact GM| s1p_model| s1p_kw]
            | eapply gm_push_gen; [exact GM| s1p_model| s1p_arith| s1p_arith| s1p_kw| s1p_cell] ]
  (* [comment removed for export] *)
  | GM : g_main ?d ?M ?a1 ?j ?dd ?er |- g_str ?d _ _ _ _ _ _ =>
      eapply gm_to_str_gen; [exact GM| s1p_model| s1p_arith| s1p_kw| s1p_cell]
  | GM : g_main ?d ?M ?a1 ?j ?dd ?er |- g_prim ?d _ _ _ _ _ _ =>
      eapply gm_to_prim_gen; [exact GM| s1p_model| s1p_arith| s1p_lin; s1m_side| s1p_arith| s1p_kw| s1p_cell]
  | GM : g_main ?d ?M ?a1 ?j ?dd ?er |- g_prim0 ?d _ _ _ _ _ _ =>
      eapply gm_to_prim0_gen; [exact GM| s1p_model| s1p_arith| s1p_kw| s1p_cell]
  (* [comment removed for export] *)
  | GP : g_prim0 ?d ?M ?a1 ?i ?k ?dd ?er |- g_prim0 ?d _ _ _ _ _ _ =>
      eapply gp0_step; [exact GP| s1p_keep| s1p_arith| s1p_arith| s1p_lin; s1m_side]
  | GP : g_prim0 ?d ?M ?a1 ?i ?k ?dd ?er |- g_main ?d _ _ _ _ _ =>
      eapply gp0_to_main; [exact GP| s1p_keep| s1p_lin; first [left; lia| right; s1m_side]| s1p_arith| s1p_arith]
  (* [comment removed for export] *)
  | GS : g_str ?d ?M ?a1 ?i ?k ?dd ?er |- g_str ?d _ _ _ _ _ _ =>
      eapply gs_same; [exact GS| s1p_keep| s1p_lin; s1m_run]
  | GS : g_str ?d ?M ?a1 ?i ?k ?dd ?er |- g_main ?d _ _ _ _ _ =>
      eapply gs_to_main; [exact GS| s1p_keep| s1p_arith| let acc := fresh "acc" in intros acc; s1p_lin; s1m_run]
  (* [comment removed for export] *)
  | GP : g_prim ?d ?M ?a1 ?i ?k ?dd ?er |- g_prim ?d _ _ _ _ _ _ =>
      eapply gp_same_gen; [exact GP| s1p_arith| s1p_arith| s1p_lin; s1m_side| s1p_kw]
  | GP : g_prim ?d ?M ?a1 ?i ?k ?dd ?er |- g_main ?d _ _ _ _ _ =>
      eapply gp_to_main_gen; [exact GP| s1p_lin; first [left; lia| right; s1m_side]| s1p_arith| s1p_arith| s1p_kw]
  end.

(* [comment removed for export] *)
Lemma edenot_var_lin : forall segs E m kn e n, know_ok segs E m kn -> lin_nowrap kn e = true -> lin_of e = (0, [(1, EVar n)]) ->
  edenot E e = ev E n.
Proof.
  intros segs E m kn e n HK HN HL. apply w_eq. rewrite (VP.u_lin' segs E m kn e _ HK HN HL). reflexivity.
Qed.
Ltac s1p_tnorm :=
  repeat match goal with
  | HK : know_ok ?segs ?E ?m ?kn |- context [edenot ?E ?e] =>
      lazymatch e with EVar _ => fail | ELit _ => fail | _ => idtac end;
      let l := eval vm_compute in (lin_of e) in
      lazymatch l with
      | (0, [(1, EVar ?n)]) =>
          rewrite (edenot_var_lin segs E m kn e n HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
      end
  end.

Ltac s1p_unlog := try (match goal with LG := _ : list sentry |- _ => unfold LG in *; clear LG end).

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma rev_cons_app : forall (x : Z) l C, rev (x :: l) ++ C = rev l ++ x :: C.
Proof. intros x l C. cbn [rev]. rewrite <- app_assoc. reflexivity. Qed.

Lemma gx_len0 : forall d M a1 rc n this, zlength d = 0 -> bv_unsigned rc <> 0 -> g_exit d M a1 rc n this.
Proof.
  intros d M a1 rc n this H0 H1. destruct d as [|x r]; [|unfold zlength in H0; cbn [length] in H0; lia].
  unfold g_exit. split; [split; [intros; contradiction| cbn; discriminate]| intros; contradiction].
Qed.

Lemma gm_init : forall d M a1, g_main d M a1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).
Proof.
  intros d M a1. pose proof (ur a1) as H. exists []. split; [reflexivity|]. split; [change (bv_unsigned (Z_to_bv 64 0)) with 0; lia|].
  split; [intros i Hi; cbn in Hi; lia|]. rewrite scan_S1C. reflexivity.
Qed.

Lemma map_bvu_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma gtab_log : forall segs E M kn lg ns, know_ok segs E M kn -> log_flat E lg ->
  option_map (map bv_unsigned) (SV.log_lit_read kn lg (EVar ns) (-400) 256) = Some (map bv_unsigned ctab_bytes) ->
  400 <= bv_unsigned (ev E ns) -> g_tab (mem_denot E M lg) (ev E ns).
Proof.
  intros segs E M kn lg ns HK HL HR0 H4. split; [exact H4|].
  assert (HR : SV.log_lit_read kn lg (EVar ns) (-400) 256 = Some ctab_bytes).
  { destruct (SV.log_lit_read kn lg (EVar ns) (-400) 256) as [bs|]; [|discriminate]. cbn [option_map] in HR0.
    assert (Hb : map bv_unsigned bs = map bv_unsigned ctab_bytes) by congruence. apply map_bvu_inj in Hb. subst bs. reflexivity. }
  pose proof (ur (ev E ns)) as U.
  destruct (SV.log_lit_read_sound segs E M M kn lg (EVar ns) 256 (-400) ctab_bytes HK HL ltac:(cbn [edenot]; lia) ltac:(cbn [edenot]; lia) HR)
    as [_ HB].
  intros i Hi. unfold ctab_bytes in Hi. rewrite length_map, length_seq in Hi.
  specialize (HB (Z.to_nat i) ltac:(lia)). cbn [edenot] in HB. rewrite Z2Nat.id in HB by lia.
  replace (bv_unsigned (ev E ns) - 400 + i) with (bv_unsigned (ev E ns) + -400 + i) by lia. exact HB.
Qed.



(* [comment removed for export] *)
Ltac s1p_cells :=
  lazymatch goal with
  | |- mbytes _ _ (u32bytes []) => apply mbytes_nil
  | |- mbytes _ _ (u32bytes (_ :: _)) => apply mbytes_u32_cons; [s1p_cell| s1p_cells]
  end.

(* [comment removed for export] *)
Ltac s1p_xmem Hm :=
  unfold xmem; s1p_lin; s1p_pow;
  lazymatch goal with
  | |- _ /\ _ /\ mbytes ?M ?A (u32bytes (rev ?X ++ ?C)) /\ _ /\ _ =>
      split; [rewrite ?zlength_cons; lia|]; split; [lia|]; split;
      [ first
        [ apply mbytes_u32_app;
            [ lazymatch goal with HL : log_flat ?E ?lg |- _ =>
                apply (mbytes_log_out E _ lg); [exact HL| lia| rewrite u32bytes_len, ?zlength_rev', ?zlength_cons; lia| | exact Hm];
                let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; rewrite u32bytes_len, ?zlength_rev', ?zlength_cons in Hi;
                cbn [SV.outside_log]; s1p_lin; repeat split; s1p_alia end
            | rewrite ?zlength_rev', ?zlength_cons; s1p_cells ]
        | rewrite rev_cons_app; apply mbytes_u32_app;
            [ lazymatch goal with HL : log_flat ?E ?lg |- _ =>
                apply (mbytes_log_out E _ lg); [exact HL| lia| rewrite u32bytes_len, ?zlength_rev', ?zlength_cons; lia| | exact Hm];
                let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; rewrite u32bytes_len, ?zlength_rev', ?zlength_cons in Hi;
                cbn [SV.outside_log]; s1p_lin; repeat split; s1p_alia end
            | rewrite ?zlength_rev', ?zlength_cons; s1p_cells ] ]
      | split; [lia| s1p_cell] ]
  end.

(* [comment removed for export] *)
Ltac s1p_rc :=
  let acc := fresh "acc" in let Hacc := fresh "Hacc" in intros acc Hacc; cbv beta; s1p_lin_hyps;
  first
  [ apply rc_fail; [s1p_lin; lia| first [apply fin3_uncl | (destruct acc; [reflexivity| exfalso; rewrite zlength_cons in Hacc; unfold zlength in Hacc; s1p_lin; s1p_pow; lia])]]
  | apply rc_err; first [discriminate | (destruct acc; [exfalso; unfold zlength in Hacc; cbn [length Z.of_nat] in Hacc; s1p_lin; s1p_pow; lia| discriminate])] ].

Ltac s1p_xrun := let acc := fresh "acc" in intros acc; s1p_lin;
  repeat (lazymatch goal with |- fin3 _ = _ => fail | _ => s1m_step end); reflexivity.
Ltac s1p_xm := let acc := fresh "acc" in let Hacc := fresh "Hacc" in let Hb := fresh "Hb" in let Hm := fresh "Hm" in let Hrc := fresh "Hrc" in
  intros acc Hacc Hb Hm Hrc; cbv beta; s1p_lin_hyps; first [ (exfalso; revert Hrc; s1p_lin; lia) | s1p_xmem Hm ].

(* [comment removed for export] *)
Ltac s1p_exit :=
  lazymatch goal with
  | GM : g_main ?d ?M ?a1 ?j ?dd ?er |- g_exit ?d _ _ _ _ _ => eapply gm_exit; [exact GM| s1p_xrun| s1p_rc| s1p_xm]
  | GS : g_str ?d ?M ?a1 ?i ?k ?dd ?er |- g_exit ?d _ _ _ _ _ => eapply gs_exit; [exact GS| s1p_xrun| s1p_rc| s1p_xm]
  | GP : g_prim ?d ?M ?a1 ?i ?k ?dd ?er |- g_exit ?d _ _ _ _ _ =>
      eapply gp_exit; [exact GP| let acc := fresh "acc" in let H1 := fresh in let H2 := fresh in intros acc H1 H2; s1p_lin;
                                 repeat (lazymatch goal with |- fin3 _ = _ => fail | _ => s1m_step end); reflexivity
                      | s1p_rc| s1p_xm]
  | GP : g_prim0 ?d ?M ?a1 ?i ?k ?dd ?er |- g_exit ?d _ _ _ _ _ => eapply gp0_exit; [exact GP| s1p_xrun| s1p_rc| s1p_xm]
  | GB : g_buf ?d _ _ _ |- g_exit ?d _ _ _ _ _ => apply gx_len0; [lia| s1p_lin; lia]
  end.
(* [comment removed for export] *)
Ltac s1p_entry :=
  lazymatch goal with
  | HK : know_ok ?segs ?E ?m ?kn, HL : log_flat ?E ?lg |- g_tab (mem_denot ?E ?m ?lg) (ev ?E ?ns) =>
      apply (gtab_log segs E m kn lg ns HK HL); [vm_compute; reflexivity| lia]
  | |- g_main _ _ _ (edenot _ (ELit 0)) (edenot _ (ELit 0)) (edenot _ (ELit 0)) => apply gm_init
  end.

(* [comment removed for export] *)
Lemma ias_true : forall b, is_ascii_stop b = true -> b < 32 \/ b = 34 \/ b = 92 \/ 128 <= b.
Proof. intros b H. unfold is_ascii_stop in H. repeat rewrite orb_true_iff in H. rewrite Z.ltb_lt, !Z.eqb_eq, Z.leb_le in H. tauto. Qed.
Lemma ias_false : forall b, is_ascii_stop b = false -> 32 <= b < 128 /\ b <> 34 /\ b <> 92.
Proof. intros b H. unfold is_ascii_stop in H. repeat rewrite orb_false_iff in H. rewrite Z.ltb_ge, !Z.eqb_neq, Z.leb_gt in H. lia. Qed.
Ltac s1p_contra :=
  repeat match goal with
  | H : is_ascii_stop _ = true |- _ => apply ias_true in H
  | H : is_ascii_stop _ = false |- _ => apply ias_false in H
  end; lia.

Ltac s1p_solve := s1p_pre; s1vc_cls; s1p_unlog; s1p_tgt; s1p_tnorm; first [s1p_edge | s1p_exit | s1p_entry | (exfalso; s1p_contra)].
