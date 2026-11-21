(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 BitsLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 TreesRod6 TreesApi6 CompressBlk6_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma tree_dl_set_bi_buf : forall s j t', tree_dl (set_bi_buf s j) t' = tree_dl s t'.
Proof. intros s j [| |]; reflexivity. Qed.
Lemma tree_fc_set_bi_buf : forall s j t', tree_fc (set_bi_buf s j) t' = tree_fc s t'.
Proof. intros s j [| |]; reflexivity. Qed.

Lemma mod16_congr : forall a b, a = b -> a mod 2 ^ 16 = b mod 2 ^ 16.
Proof. intros a b ->. reflexivity. Qed.
Lemma mod16_up : forall a b, a = b + 65536 -> a mod 2 ^ 16 = b mod 2 ^ 16.
Proof. intros a b ->. change 65536 with (1 * 2 ^ 16). rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma wrap16_id' : forall v x, v = x -> 0 <= x < 2 ^ 16 -> v = wrap16 x.
Proof. intros v x -> Hx. symmetry. apply wrap16_id. exact Hx. Qed.
Lemma land16_mod : forall a, Z.land a 65535 = a mod 2 ^ 16.
Proof. intros a. change 65535 with (Z.ones 16). apply Z.land_ones. lia. Qed.
Lemma land16_range : forall a, 0 <= Z.land a 65535 < 2 ^ 16.
Proof. intros a. rewrite land16_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma land16_wrap16 : forall a v, a mod 2 ^ 16 = v mod 2 ^ 16 -> Z.land a 65535 = wrap16 v.
Proof. intros a v E. rewrite land16_mod, wrap16_mod'. exact E. Qed.

Lemma zaluw_u64 : forall op a b, 0 <= zaluw op a b < 2 ^ 64.
Proof. intros. unfold zaluw. apply u64_range. Qed.

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.

Lemma lxor_eqb : forall a b, (Z.lxor a b =? 0) = (a =? b).
Proof.
  intros a b. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.eqb_neq. intros E. apply NE. apply Z.lxor_eq_0_iff. exact E.
Qed.

Lemma lxor_ltb1 : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b <? 1) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)).
    assert (Z.lxor a b <> 0) by (intros E; apply NE; apply Z.lxor_eq_0_iff; exact E). lia.
Qed.


Record STH (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
       (ds : deflate_state) (ra : word) (sp : Z) (t : tree_id) (mc : Z) : Prop := {
  sth_ret : ret_ok ra;
  sth_L : BRH F S p PBL;
  sth_fr : call_frame F mem S (p_pending_buf p) PBL sp 80;
  sth_br : BR6 F mem0 S p PBL mem ds;
  sth_t : t = TL \/ t = TD;
  sth_mc : 0 <= mc /\ mc + 1 < tsize t;
  sth_len : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15;
  sth_dl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl ds t) i < 65536;
  sth_bc : forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc ds) c < 65536;
  sth_bl : forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl ds) c < 16;
  sth_binv : BINV PBL ds;
  sth_pbl : 0 < PBL }.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variables (t : tree_id) (mc : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation T := (S + toff t).
Local Abbreviation SP := (sp - 80).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).
Local Abbreviation L i := (Len ds t i).
Local Abbreviation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Abbreviation BL c := (arr_get (ds_bl_tree_dl ds) c).

Hypothesis HH : STH F mem0 mem S p PBL ds ra sp t mc.

Let Hret : ret_ok ra := sth_ret _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := sth_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hfr80 : call_frame F mem S PB PBL sp 80 := sth_fr _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := sth_br _ _ _ _ _ _ _ _ _ _ _ HH.
Let Ht : t = TL \/ t = TD := sth_t _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hmc : 0 <= mc /\ mc + 1 < tsize t := sth_mc _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15 := sth_len _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl ds t) i < 65536 := sth_dl _ _ _ _ _ _ _ _ _ _ _ HH.
Let HbC : forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc ds) c < 65536 := sth_bc _ _ _ _ _ _ _ _ _ _ _ HH.
Let HbL : forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl ds) c < 16 := sth_bl _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hbinv : BINV PBL ds := sth_binv _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := sth_pbl _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 80 <= sp <= 2 ^ 63 := proj1 Hfr80.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.

Definition PURE (s : deflate_state) : Prop :=
  BINV PBL s
  /\ (forall t', tree_fc s t' = tree_fc ds t') /\ (forall t', tree_dl s t' = tree_dl ds t')
  /\ arr_len (ds_pending_buf s) = PBL /\ tree_lens s.

Definition GI : franges := [(S, 5968); (PB, PBL)].

Definition CI (m0 m : word -> option byte) (s : deflate_state) : Prop :=
  BRm m s /\ PURE s /\ agree_out GI m0 m.

Lemma PURE_send : forall s v l, PURE s -> 0 <= l <= 16 -> sb_room PBL s l -> PURE (send_bits s v l).
Proof.
  intros s v l (P1 & P2 & P3 & P4 & P5) Hl Hr. unfold PURE.
  split; [apply send_bits_BINV; assumption|].
  split; [intros t'; rewrite sb_tree_fc; apply P2|]. split; [intros t'; rewrite sb_tree_dl; apply P3|].
  split; [rewrite sb_pbl; exact P4 | apply sb_lens; exact P5].
Qed.

Lemma PURE_Len : forall s i, PURE s -> Len s t i = L i.
Proof. intros s i (_ & _ & P3 & _). unfold Len. rewrite P3. reflexivity. Qed.
Lemma PURE_blc : forall s c, PURE s -> blc s c = (BC c, BL c).
Proof. intros s c (_ & P2 & P3 & _). unfold blc, Code, Len. rewrite P2, P3. reflexivity. Qed.

Definition RBr (r : reg) (R : bvmap 5 word) (s : deflate_state) : Prop :=
  (bv_unsigned (getr R r)) mod 2 ^ 16 = ds_bi_buf s.

Definition KREGS (R : bvmap 5 word) : Prop :=
  getr R 10 = zw S /\ getr R 11 = zw T /\ getr R 12 = zw (mc + 1) /\ getr R 13 = zw (S + 2047)
  /\ getr R 16 = zw (S + 5936) /\ getr R 17 = zw 65535 /\ getr R 5 = zw (S + 2748)
  /\ getr R 6 = zw 16 /\ getr R 7 = zw 4 /\ getr R 28 = zw 9 /\ getr R 29 = zw 14
  /\ getr R 30 = zw 10 /\ getr R 31 = zw 15 /\ getr R 2 = zw SP.

Definition HREGS (R : bvmap 5 word) (n pl c k mx mn : Z) : Prop :=
  KREGS R /\ getr R 14 = zw c /\ getr R 15 = zw n /\ getr R 9 = zw k
  /\ getr R 19 = zw mx /\ getr R 20 = zw mn /\ getr R 21 = zw pl.

Definition DREGS (R : bvmap 5 word) (n pl c nl k mx mn : Z) : Prop :=
  KREGS R /\ getr R 8 = zw c /\ getr R 15 = zw (n + 1) /\ getr R 14 = zw nl
  /\ getr R 18 = zw (k + 1) /\ getr R 9 = zw k
  /\ getr R 19 = zw mx /\ getr R 20 = zw mn /\ getr R 21 = zw pl.

Definition GREGS (R : bvmap 5 word) (n c nl : Z) : Prop :=
  KREGS R /\ getr R 8 = zw c /\ getr R 15 = zw (n + 1) /\ getr R 14 = zw nl /\ getr R 18 = zw 0.

Definition TGT (nl : Z) : word := if nl =? 0 then (0x1cc34 : word) else (0x1c860 : word).

Definition CLOBI : list reg := [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%bv.
Definition ST_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.


Definition stF (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb (tree_dl ds t) x | 1%nat => pb (ds_bl_tree_fc ds) x | _ => pb (ds_bl_tree_dl ds) x end.

Definition stC : cfg := CFG [(0%nat, 65536); (1%nat, 65536); (2%nat, 65536)] [] [EVar 1%nat]
  [0x1c79c; 0x1c7bc; 0x1c828; 0x1c858; 0x1ca34; 0x1c860; 0x1cc34; 0x1cc40;
   0x1cab0; 0x1cae4; 0x1c908; 0x1cb5c; 0x1ca10; 0x1cbd4] [].

Definition KP : list (Z * expr) :=
  [(10, EVar 32); (11, EVar 36); (12, EAdd (EVar 37) (ELit 1)); (13, EAdd (EVar 32) (ELit 2047));
   (16, EAdd (EVar 32) (ELit 5936)); (17, ELit 65535); (5, EAdd (EVar 32) (ELit 2748));
   (6, ELit 16); (7, ELit 4); (28, ELit 9); (29, ELit 14); (30, ELit 10); (31, ELit 15); (2, EVar 45)].

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 2 ^ 63); (37%nat, 600); (38%nat, 600);
   (39%nat, 16); (40%nat, 65536); (41%nat, 200); (42%nat, 65536); (43%nat, 200); (44%nat, 10); (45%nat, 2 ^ 63);
   (46%nat, 200); (47%nat, 65536); (48%nat, 2 ^ 64);
   (49%nat, 2 ^ 64); (50%nat, 2 ^ 64); (51%nat, 2 ^ 64); (52%nat, 2 ^ 64); (53%nat, 2 ^ 64); (54%nat, 2 ^ 64);
   (55%nat, 2 ^ 64); (56%nat, 2 ^ 64); (57%nat, 2 ^ 64)].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [stF].

Local Ltac st_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = pb ?tt ?i =>
      match goal with H : cells sg m ?P 4 2%nat ?len (arr_get tt) |- _ =>
        eapply (pb_read4m sg m P len tt i a H); [lia | lia] end
  end.

Local Ltac side_closer :=
  try solve [ assumption
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; st_read
            | zcond_close
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; apply pb_range ].

Local Ltac run_with vb fuel dirs rds pins pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs stC fuel dirs rdv pinsv vbv NoRegions pv NoVals stF F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run fuel dirs rds pins pv := run_with VB fuel dirs rds pins pv.
Local Ltac run_dbg fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex_dbg s6_segs stC fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6_rom)
  end.

Local Ltac open_br HB HP :=
  let P1 := fresh "Pbinv" in let P2 := fresh "Pfc" in let P3 := fresh "Pdl" in let P4 := fresh "Plen" in let P5 := fresh "Plens" in
  pose proof HP as HP'; destruct HP' as (P1 & P2 & P3 & P4 & P5);
  let Hbv := fresh "Hbv" in let Hbb := fresh "Hbb" in let Hpd := fresh "Hpd" in
  pose proof P1 as HBI'; destruct HBI' as (Hbv & Hbb & Hpd);
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in let Har := fresh "Har" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & _ & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let C40 := fresh "C40" in let C16 := fresh "C16" in let C5936 := fresh "C5936" in let C5940 := fresh "C5940" in
  let Cpb := fresh "Cpb" in
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB) as (C40 & C16 & C5936 & C5940 & Cpb); dsred in C40; dsred in C5940; dsred in C5936; dsred in Cpb;
  let TDl := fresh "TDl" in let BLc := fresh "BLc" in let BLd := fresh "BLd" in
  pose proof (arrays_dl s6_segs _ _ _ t Har) as TDl; pose proof (arrays_fc s6_segs _ _ _ TB Har) as BLc;
  pose proof (arrays_dl s6_segs _ _ _ TB Har) as BLd; cbn [toff tsize] in BLc, BLd;
  rewrite ?tree_dl_set_bi_buf in TDl; rewrite ?tree_fc_set_bi_buf in BLc; rewrite ?tree_dl_set_bi_buf in BLd;
  try rewrite (P3 t) in TDl; try rewrite (P2 TB) in BLc; try rewrite (P3 TB) in BLd;
  cbn [tree_fc tree_dl] in BLc, BLd;
  replace (S + 2748 + 2) with (S + 2750) in BLd by lia;
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let Hmc' := fresh "Hmc'" in pose proof Hmc as Hmc'.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold GI;
              first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac kregs HR Hfr :=
  unfold KREGS; repeat split;
  lazymatch goal with |- getr ?R ?r = _ =>
    first [ rewrite (Hfr r eq_refl); assumption
          | let A := fresh "A" in symex_reg HR r as A; rewrite A;
            first [ reflexivity | f_equal; lia
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] ]
  end.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [reflexivity | assumption | f_equal; lia | f_equal; f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] end
        | idtac ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac vcongr := first [ reflexivity | apply pb_mod16 | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite szwrap32_mod16, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                           | apply mod16_congr; lia
                           | apply mod16_up; lia
                           | rewrite land16_mod; first [apply mod16_congr; lia | apply mod16_up; lia]
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vwrap := first [ reflexivity | apply pb_wrap16 | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                          | apply wrap16_id'; lia
                          | apply land16_wrap16; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia | apply land16_range ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia
                        | lazymatch goal with H : RBr _ _ _ |- _ => exact H end ].

Local Ltac st_flush vnorm :=
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); st_eq;
  [ vnorm; f_equal;
    [ f_equal; [lia | apply byte0_eq; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
    | lia
    | apply byte1_eq2; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr] ]
  | lia
  | first [reflexivity | vnorm; apply srl_eq'; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; apply srl_eq'; [vrange | vwrap | lia].
Local Ltac bv_flush r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia.
Local Ltac st_keep vnorm :=
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); st_eq;
  [ reflexivity
  | reflexivity
  | first [reflexivity | vnorm; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); lia] ].
Local Ltac rb_keep r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr].
Local Ltac bv_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); lia.
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].

Local Ltac site_fin Hms HR Hfr HB HP HAG tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [pure_fin HP | ag_tower HAG] ]
                 | tregs ]
      end
  end.

Local Ltac site_finx Hms HR Hfr HB HP HAG tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eexists; eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [pure_fin HP | ag_tower HAG] ]
                 | tregs ]
      end
  end.

Local Ltac cnt_reg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
    let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
    rewrite ?lxor_ltb1 by lia; rewrite ?Z.eqb_refl;
    try (replace (_ =? _) with false by (symmetry; apply Z.eqb_neq; lia));
    vm_compute; reflexivity
  end.

Local Ltac kd H := destruct H as (K10 & K11 & K12 & K13 & K16 & K17 & K5 & K6 & K7 & K28 & K29 & K30 & K31 & K2).


Local Ltac hregs H := destruct H as (HK & P14 & P15 & P9 & P19 & P20 & P21).

Definition HP (plp : list (Z * expr)) : list (Z * expr) :=
  KP ++ [(14, EVar 39); (15, EVar 38); (9, EVar 41); (19, EVar 43); (20, EVar 44)] ++ plp.

Lemma h_emit : forall regs m0 m s n pl c k mx mn,
  CI m0 m s -> HREGS regs n pl c k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (mx <= k + 1 \/ c <> L (n + 1)) ->
  exists R,
    msteps s6_segs (mkst regs (0x1c79c : word) m s6_rom) (mkst R (0x1c7bc : word) m s6_rom)
    /\ DREGS R n pl c (L (n + 1)) k mx mn
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s n pl c k mx mn (HB & HPu & HAG) HRg Hn Hc Hk Hmx Hmn Hcase.
  open_br HB HPu. hregs HRg. kd HK.
  pose proof (Hdl (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl ds t) (n + 1) = L (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  destruct (Z_le_gt_dec mx (k + 1)) as [C1|C1].
  - run 40%nat [true] [RVal (EApp1 0 (EAdd (EVar 38) (ELit 1)))] (HP [])
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; 0; k; 0; mx; mn; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr].
    unfold DREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
  - run 40%nat [false; false] [RVal (EApp1 0 (EAdd (EVar 38) (ELit 1)))] (HP [])
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; 0; k; 0; mx; mn; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr].
    unfold DREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma h_cont : forall regs m0 m s n pl c k mx mn,
  CI m0 m s -> HREGS regs n pl c k mx mn -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  k + 1 < mx -> c = L (n + 1) ->
  exists R,
    msteps s6_segs (mkst regs (0x1c79c : word) m s6_rom)
           (mkst R (if n + 1 =? mc + 1 then (0x1cc40 : word) else (0x1c79c : word)) m s6_rom)
    /\ HREGS R (n + 1) pl c (k + 1) mx mn
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s n pl c k mx mn (HB & HPu & HAG) HRg Hn Hc Hk Hmx Hmn C1 Ec.
  open_br HB HPu. hregs HRg. kd HK.
  pose proof (Hdl (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl ds t) (n + 1) = L (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
  - run 40%nat [false; true; true] [RVal (EApp1 0 (EAdd (EVar 38) (ELit 1)))] (HP [])
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; 0; k; 0; mx; mn; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr].
    unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
  - run 40%nat [false; true; false] [RVal (EApp1 0 (EAdd (EVar 38) (ELit 1)))] (HP [])
        [S; PB; ds_pending s; ds_bi_valid s; T; mc; n; c; 0; k; 0; mx; mn; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr].
    unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.


Local Ltac gregs H := destruct H as (HK & P8 & P15 & P14 & P18).

Definition GP : list (Z * expr) := KP ++ [(8, EVar 39); (15, EAdd (EVar 38) (ELit 1)); (14, EVar 40); (18, ELit 0)].

Definition cntsnz (c nl : Z) : Z * Z := if c =? nl then (6, 3) else (7, 4).

Lemma tnz_blk : forall regs m n c nl,
  GREGS regs n c nl -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 < nl < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1c860 : word) m s6_rom)
           (mkst R (if n + 1 =? mc + 1 then (0x1cc40 : word) else (0x1c79c : word)) m s6_rom)
    /\ HREGS R (n + 1) c nl 0 (fst (cntsnz c nl)) (snd (cntsnz c nl))
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m n c nl HG Hn Hc Hnl. gregs HG. kd HK.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof Hmc as Hmc'.
  unfold cntsnz.
  destruct (Z.eqb_spec c nl) as [Ecn|Ecn]; destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En]; cbn [fst snd].
  - subst c. run 30%nat [true] NoReads GP [S; 0; 0; 0; T; mc; n; nl; nl; 0; 0; 0; 0; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
    all: cnt_reg HR.
  - subst c. run 30%nat [false] NoReads GP [S; 0; 0; 0; T; mc; n; nl; nl; 0; 0; 0; 0; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
    all: cnt_reg HR.
  - run 30%nat [true] NoReads GP [S; 0; 0; 0; T; mc; n; c; nl; 0; 0; 0; 0; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
    all: cnt_reg HR.
  - run 30%nat [false] NoReads GP [S; 0; 0; 0; T; mc; n; c; nl; 0; 0; 0; 0; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
    all: cnt_reg HR.
Qed.

Lemma tz_blk : forall regs m n c,
  GREGS regs n c 0 -> 0 <= n <= mc -> 0 <= c <= 15 ->
  exists R,
    msteps s6_segs (mkst regs (0x1cc34 : word) m s6_rom)
           (mkst R (if n + 1 =? mc + 1 then (0x1cc40 : word) else (0x1c79c : word)) m s6_rom)
    /\ HREGS R (n + 1) c 0 0 138 3
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m n c HG Hn Hc. gregs HG. kd HK.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof Hmc as Hmc'.
  destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
  - run 30%nat [true] NoReads GP [S; 0; 0; 0; T; mc; n; c; 0; 0; 0; 0; 0; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
  - run 30%nat [false] NoReads GP [S; 0; 0; 0; T; mc; n; c; 0; 0; 0; 0; 0; SP; 0; 0].
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold HREGS. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.


Definition FRAME (m : word -> option byte) (v : list Z) : Prop :=
  match v with
  | [v0; v1; v2; v3; v4; v5; v6; v7; v8] =>
      cell s6_segs m (SP + 72) 8 v0 /\ cell s6_segs m (SP + 64) 8 v1 /\ cell s6_segs m (SP + 56) 8 v2
      /\ cell s6_segs m (SP + 48) 8 v3 /\ cell s6_segs m (SP + 40) 8 v4 /\ cell s6_segs m (SP + 32) 8 v5
      /\ cell s6_segs m (SP + 24) 8 v6 /\ cell s6_segs m (SP + 16) 8 v7 /\ cell s6_segs m (SP + 8) 8 v8
      /\ Forall (fun x => 0 <= x < 2 ^ 64) v
  | _ => False
  end.

Lemma exit_blk : forall regs m v0 v1 v2 v3 v4 v5 v6 v7 v8,
  KREGS regs -> getr regs 1 = ra -> FRAME m [v0; v1; v2; v3; v4; v5; v6; v7; v8] -> mapped m SP 80 ->
  exists R,
    msteps s6_segs (mkst regs (0x1cc40 : word) m s6_rom) (mkst R ra m s6_rom)
    /\ getr R 8 = zw v0 /\ getr R 9 = zw v1 /\ getr R 18 = zw v2 /\ getr R 19 = zw v3
    /\ getr R 20 = zw v4 /\ getr R 21 = zw v5 /\ getr R 22 = zw v6 /\ getr R 23 = zw v7 /\ getr R 24 = zw v8
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m v0 v1 v2 v3 v4 v5 v6 v7 v8 K P1 (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & U) MF. kd K.
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
  pose proof HLb as (HS' & HPB' & _); unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'. pose proof Hmc as Hmc'.
  pose proof Hret as Hret'. unfold mapped in MF.
  run 20%nat NoDirs [RVal (EVar 49); RVal (EVar 50); RVal (EVar 51); RVal (EVar 52); RVal (EVar 53); RVal (EVar 54);
                    RVal (EVar 55); RVal (EVar 56); RVal (EVar 57)] KP
      [S; PB; 0; 0; T; mc; 0; 0; 0; 0; 0; 0; 0; SP; 0; 0; 0; v0; v1; v2; v3; v4; v5; v6; v7; v8].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ _ _) =>
      exists R; split; [rewrite <- P1; exact Hms|]; clear Hms
  end.
  repeat split; try (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; first [reflexivity | f_equal; lia] end).
  fr_weak Hfr.
Qed.


Definition cnts0 : Z * Z := if L 0 =? 0 then (138, 3) else (7, 4).

Lemma pro_blk : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw T -> getr regs 12 = zw mc -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  PURE ds ->
  exists R m1,
    msteps s6_segs (mkst regs (0x1c6fc : word) mem s6_rom) (mkst R (0x1c79c : word) m1 s6_rom)
    /\ CI m1 m1 ds
    /\ HREGS R 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0)
    /\ getr R 1 = ra
    /\ FRAME m1 [bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18);
                 bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21);
                 bv_unsigned (getr regs 22); bv_unsigned (getr regs 23); bv_unsigned (getr regs 24)]
    /\ mapped m1 SP 80
    /\ (forall r : reg, reg_in r (2 :: CLOBI)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P2 P1 HPu.
  pose proof HBR0 as HB. open_br HB HPu.
  pose proof Hfr80 as (_ & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS. pose proof Hmf as MF. unfold mapped in MF.
  pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19.
  pose proof (u64_range (getr regs 20)) as U20. pose proof (u64_range (getr regs 21)) as U21.
  pose proof (u64_range (getr regs 22)) as U22. pose proof (u64_range (getr regs 23)) as U23.
  pose proof (u64_range (getr regs 24)) as U24.
  assert (P2' : getr regs 2 = zw (SP + 80)) by (rewrite P2; f_equal; lia).
  pose proof (Hdl 0 ltac:(lia)) as R0. pose proof (Hlen 0 ltac:(lia)) as V0.
  assert (E0 : pb (tree_dl ds t) 0 = L 0) by (unfold Len; apply pb_small; exact R0).
  assert (BRfr : forall M s0, BRm M s0 ->
    forall b v, SP <= b -> b + 8 <= sp ->
    BRm (wbytes M (zw b) (Z_to_le_bytes 8 v)) s0).
  { intros M s0 HM b v Hb1 Hb2.
    apply (BR_st_other _ _ _ _ F mem0 S p PBL HLb); [exact HM | lia | rewrite length_Z_to_le_bytes; cbn; lia
      | rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia
      | rewrite length_Z_to_le_bytes; eapply sub_franges_mono; [exact HFf | cbn; lia | cbn; lia] ]. }
  assert (FIN : forall R M,
    msteps s6_segs (mkst regs (0x1c6fc : word) mem s6_rom) (mkst R (0x1c79c : word) M s6_rom) ->
    M = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
          (zw (SP + 72)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 8))))
          (zw (SP + 64)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 9))))
          (zw (SP + 56)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 18))))
          (zw (SP + 48)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 19))))
          (zw (SP + 40)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 20))))
          (zw (SP + 32)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 21))))
          (zw (SP + 24)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 22))))
          (zw (SP + 16)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 23))))
          (zw (SP + 8)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 24))) ->
    HREGS R 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0) -> getr R 1 = ra ->
    (forall r : reg, reg_in r (2 :: CLOBI)%bv = false -> getr R r = getr regs r) ->
    exists R' m1,
      msteps s6_segs (mkst regs (0x1c6fc : word) mem s6_rom) (mkst R' (0x1c79c : word) m1 s6_rom)
      /\ CI m1 m1 ds
      /\ HREGS R' 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0)
      /\ getr R' 1 = ra
      /\ FRAME m1 [bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18);
                   bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21);
                   bv_unsigned (getr regs 22); bv_unsigned (getr regs 23); bv_unsigned (getr regs 24)]
      /\ mapped m1 SP 80
      /\ (forall r : reg, reg_in r (2 :: CLOBI)%bv = false -> getr R' r = getr regs r)).
  { intros R M Hms -> HRg Q1 Hfr. eexists R, _. split; [exact Hms|].
    split.
    { split; [repeat (apply BRfr; [|lia|lia]); exact HB|]. split; [exact HPu | apply agree_out_refl]. }
    split; [exact HRg|]. split; [exact Q1|].
    split.
    { unfold FRAME. repeat split; try (repeat constructor; lia);
      repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                    | apply cell_write_other; [| lia | cbn; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia] ]). }
    split; [repeat (apply mapped_wbytes); exact Hmf | exact Hfr]. }
  unfold cnts0 in *.
  destruct (Z.eqb_spec (L 0) 0) as [CZ|CZ]; cbn [fst snd] in *.
  - run 60%nat [false; true] [RVal (EApp1 0 (ELit 0))]
        [(10, EVar 32); (11, EVar 36); (12, EVar 37); (2, EAdd (EVar 45) (ELit 80))]
        [S; PB; ds_pending ds; ds_bi_valid ds; T; mc; 0; 0; 0; 0; 0; 0; 0; SP; 0; 0].
    apply (FIN R _ Hms); [reflexivity | | reg1 HR Hfr | fr_weak Hfr].
    unfold HREGS; split; [kregs HR Hfr|]; regs_of HR Hfr.
    symex_reg HR (20%bv : reg) as A; rewrite A; f_equal; nf; rewrite E0, CZ; reflexivity.
  - run 60%nat [false; false] [RVal (EApp1 0 (ELit 0))]
        [(10, EVar 32); (11, EVar 36); (12, EVar 37); (2, EAdd (EVar 45) (ELit 80))]
        [S; PB; ds_pending ds; ds_bi_valid ds; T; mc; 0; 0; 0; 0; 0; 0; 0; SP; 0; 0].
    apply (FIN R _ Hms); [reflexivity | | reg1 HR Hfr | fr_weak Hfr].
    unfold HREGS; split; [kregs HR Hfr|]; regs_of HR Hfr.
    symex_reg HR (20%bv : reg) as A; rewrite A; f_equal; nf; rewrite E0.
    replace (0 <? L 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
End Walk.
End FXG.
