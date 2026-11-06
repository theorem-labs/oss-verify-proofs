(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg LazyCfg LazyAccCfg AllocLazyCfg EagerCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn
  FxLazy FxSys FxDrive FxCellFrame FxDrive3 FxDrive3N.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shadow_region (sl : int) (p : int) : region :=
  RGK 0 sl 9 (Some PKZero) iempty clo_dflt chi_dflt (RK_shadow p).

Definition add_region (F : fstate) (t : int) (rg : region) : fstate :=
  FS (f_pc F) (f_regs F) (iset t rg (f_mem F)) (f_resv F).

(* [comment removed for export] *)
Definition sh_base (a : word) : word := Z_to_bv 64 (bv_unsigned a / 8 + to_Z shadow_K).

Section Drive3SDefs.
Local Open Scope uint63_scope.
Variable Rb Rc Lim : Z.
Variable keep : list int.
(* [comment removed for export] *)
Variable shp : int -> bool.

(* [comment removed for export] *)
Definition shadow_ledger3 (L3 : fledger3) (n1 sl : int) : fledger3 :=
  FL3 (fl3 L3) (fl_all L3) (fl_ops L3 ++ [(OpShadow, (n1, 0, sl))]) (fl_lazy L3) ((n1, 0, sl) :: fl_allow L3)
      (fl_Ab L3 + to_Z sl + 8192)%Z (fl_E L3) (fl_ex L3) (fl_ord L3) (fl_res L3).

(* [comment removed for export] *)
Definition sys_grant3p (nr : bool) (F : fstate) (L3 : fledger3) (n : int) (len : int) : option dres3 :=
  match sys_grant3 Rb Rc Lim nr F L3 n len with
  | Some (D3One F1 L31 n1) =>
      if shp (pg_up len) then
        let sl := pg_up len >> 3 in
        let L32 := shadow_ledger3 L31 n1 sl in
        if (n1 <? 1152921504606846975) && acct_ok Lim L32      (* [comment removed for export] *)
        then Some (D3One (add_region F1 n1 (shadow_region sl n)) L32 (n1 + 1)) else None
      else Some (D3One F1 L31 n1)
  | _ => None
  end.

(* [comment removed for export] *)
Definition drop_region (F : fstate) (t : int) : fstate :=
  FS (f_pc F) (f_regs F) (iremove t (f_mem F)) (f_resv F).

(* [comment removed for export] *)
Definition shadow_clean (L : fledger) (M : itrie region) (t1 : int) : bool :=
  match iget t1 M with
  | Some rg' =>
      match rg_kind rg', rg_dflt rg' with
      | RK_shadow _, Some PKZero =>
          iall (fun _ _ => false) (rg_pages rg') && (rg_lo rg' =? 0) && ((rg_len rg' land 7) =? 0)
          && (rg_len rg' <=? 4611686018427387904) && negb (t1 =? 0)
          && negb (mem_int t1 keep) && negb (t1 =? fl_brk L)
          && forallb (fun e => negb (fent_tag e =? t1)) (fl_maps L ++ fl_na L)
          && no_shadow_child M t1
      | _, _ => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Definition sys_unmap3p (F : fstate) (L3 : fledger3) (n : int) (t off len : int) : option dres3 :=
  if shadow_clean (fl3 L3) (f_mem F) (t + 1)
  then sys_unmap3 Lim keep (drop_region F (t + 1)) L3 n t off len
  else sys_unmap3 Lim keep F L3 n t off len.

(* [comment removed for export] *)
Definition span_lo_i : int := 2147446784.
Definition span_hi_i : int := 17594333495296.

Definition snap_bounds (rg : region) : int * int :=
  let len := rg_len rg in let clo := rg_clo rg in let chi := rg_chi rg in
  if (clo <? 4611686018427387904) && (len <=? 4611686018427387904) then
    ((if (span_lo_i <? clo + len) && (clo <? span_hi_i) then span_hi_i else clo),
     (if (chi <? span_hi_i) && (len <=? span_lo_i) && (span_lo_i - len <? chi) then span_lo_i - len else chi))
  else (clo, chi).

Definition snap (L : fledger) (n : int) (F : fstate) (t : int) : fstate :=
  match iget t (f_mem F) with
  | Some rg =>
      if (t <? n) && (rg_lo rg =? 0) && negb (t =? 0) && mem_fent (t, 0, rg_len rg) (fl_maps L)
      then set_bounds F t rg (fst (snap_bounds rg)) (snd (snap_bounds rg))
      else F
  | None => F
  end.

(* [comment removed for export] *)
Definition refine3 (L : fledger) (F : fstate) (n t thr : int) : option (fstate * fstate) :=
  match refine_region F n t thr with
  | Some (Fa, Fb) => Some (snap L n Fa t, snap L n Fb t)
  | None => None
  end.

End Drive3SDefs.

(* [comment removed for export] *)
Section BandAsk.
Local Open Scope uint63_scope.
Variable code : itrie finstr.

Definition ask_band_vals (a b : fval) : option (int * int) :=
  match a, b with
  | FV ta (W64 topa wa), FV tb (W64 topb wb) =>
      if (tb =? 0) && ((topb land 1) =? 0) && negb (ta =? 0) && (ta <? kind_lim)
         && ((topa land 1) =? 0) && (wa <? wb)
      then Some (ta, pg_up (wb - wa))
      else if (ta =? 0) && ((topa land 1) =? 0) && negb (tb =? 0) && (tb <? kind_lim)
              && ((topb land 1) =? 0) && (wb <=? wa)
      then Some (tb, pg_up (wa + 1 - wb))
      else None
  end.

Definition xask_band (F : fstate) : option (int * int) :=
  match iget (f_pc F) code with
  | Some (FBranch c rs1 rs2 _ _) =>
      match c with
      | BC_LTU | BC_GEU => ask_band_vals (rget F rs1) (rget F rs2)
      | _ => None
      end
  | Some (FOp ALU_SLTU _ rs1 rs2) => ask_band_vals (rget F rs1) (rget F rs2)
  | Some (FOpImm ALU_SLTU _ rs1 imm) => ask_band_vals (rget F rs1) (FV 0 imm)
  | _ => None
  end.
End BandAsk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drive3S.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Variable wb0 : word.
Variable na0 lz0 : list (word * word).
Variable brk0 : word.
(* [comment removed for export] *)
Variable A0 : list (Z * Z).

Local Abbreviation DI := (DInv cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation D3 := (DInv3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).
Local Abbreviation NE := (node_ext cfg segs IM R0 BIG RTgt keep mem0 XI xtags).
Local Abbreviation Rn := (FxRn.Rn segs IM).
Local Abbreviation erase := (FxDrive3.erase wb0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_ok_zero_v rho m t pn L wr :
  rho 0%uint63 = Z_to_bv 64 0 ->
  (forall j, 0 <= j < 8 * L ->
     rview segs m (adr rho t (to_Z pn * 4096 + j)) = Some (Z_to_bv 8 0)
     /\ wview segs m (adr rho t (to_Z pn * 4096 + j)) <> None) ->
  page_ok segs IM rho m t pn L (PG wr PKZero iempty).
Proof.
  intros H0 Hm. split; [| split];
    [| | intros ci sl _ Hget; cbn [pg_cells] in Hget; rewrite iget_iempty in Hget; discriminate Hget].
  - intros _ j Hj. exact (proj2 (Hm j Hj)).
  - intros ci v Hci Hcell j Hj. unfold cell_at in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite iget_iempty in Hcell. inversion Hcell; subst v.
    replace (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)
      with (to_Z pn * 4096 + (to_Z ci * 8 + Z.of_nat j)) by lia.
    rewrite (proj1 (Hm (to_Z ci * 8 + Z.of_nat j) ltac:(lia))).
    unfold fv0. rewrite (fk_dv_conc rho w_zero H0), wbv_w_zero. unfold wbytes8, w0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0.
    symmetry. apply fxs_zero_bytes. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_add_region rho M mem t rg :
  mem_ok segs IM rho M mem -> iget t M = None -> region_ok rho t rg ->
  (forall t' rg', iget t' M = Some rg' ->
     bv_unsigned (rho t) + to_Z (rg_len rg) <= bv_unsigned (rho t') + to_Z (rg_lo rg')
     \/ bv_unsigned (rho t') + to_Z (rg_len rg') <= bv_unsigned (rho t) + to_Z (rg_lo rg)) ->
  (forall pn p0, to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p0 ->
     page_ok segs IM rho mem t pn (clim rg pn) p0
     /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rg_len rg)
     /\ (to_Z pn * 4096 + 4096 <= to_Z (rg_len rg) \/ to_Z (rg_len rg) mod 8 = 0)) ->
  mem_ok segs IM rho (iset t rg M) mem.
Proof.
  intros [Hregs Hsep] Hfresh Hreg Hsepn Hpages. split.
  - intros t1 rg1 Hg. rewrite iget_iset in Hg. destruct (t1 =? t)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst t1. injection Hg as <-. split; [exact Hreg | exact Hpages].
    + exact (Hregs t1 rg1 Hg).
  - intros t1 t2 rg1 rg2 Hne H1 H2. rewrite iget_iset in H1, H2.
    destruct (t1 =? t)%uint63 eqn:E1; destruct (t2 =? t)%uint63 eqn:E2.
    + apply Uint63.eqb_spec in E1, E2. congruence.
    + apply Uint63.eqb_spec in E1. subst t1. injection H1 as <-. exact (Hsepn t2 rg2 H2).
    + apply Uint63.eqb_spec in E2. subst t2. injection H2 as <-.
      destruct (Hsepn t1 rg1 H1) as [Hd|Hd]; [right | left]; exact Hd.
    + exact (Hsep t1 t2 rg1 rg2 Hne H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma K_val : to_Z shadow_K = 2147450880.
Proof. reflexivity. Qed.

Lemma mod8_of_align x al : 3 <= al -> x mod 2 ^ al = 0 -> x mod 8 = 0.
Proof.
  intros Hal H.
  assert (E : 2 ^ al = 8 * 2 ^ (al - 3)).
  { replace al with (3 + (al - 3)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  apply Z.mod_divide in H; [|apply Z.pow_nonzero; lia]. destruct H as [q Hq].
  rewrite Hq, E. replace (q * (8 * 2 ^ (al - 3))) with ((q * 2 ^ (al - 3)) * 8) by ring.
  apply Z_mod_mult.
Qed.

Lemma shadow_sep_all n rho F L3 ms m p rgp (y : Z) t rg :
  D3 n rho F L3 ms m ->
  iget p (f_mem F) = Some rgp -> iget (p + 1)%uint63 (f_mem F) = None ->
  to_Z (rg_lo rgp) = 0 -> 3 <= to_Z (rg_align rgp) ->
  (bv_unsigned (rho p) + to_Z (rg_len rgp) <= span_lo \/ span_hi <= bv_unsigned (rho p)) ->
  bv_unsigned (rho p) + to_Z (rg_len rgp) <= 2 ^ 47 ->
  In (p, 0%uint63, rg_len rgp) (fl_maps (fl3 L3)) ->
  bv_unsigned (rho p) / 8 + to_Z shadow_K <= y ->
  8 * (y - (bv_unsigned (rho p) / 8 + to_Z shadow_K)) + 8 <= to_Z (rg_len rgp) ->
  iget t (f_mem F) = Some rg -> in_ival rho t rg y -> False.
Proof.
  intros (HDI & HL & HS & HX) Hgp Hfresh Hlo0 Halp Hmiss H47 Hwhole Hy1 Hy2 Hg Hin.
  pose proof HDI as (HRn & H0 & _ & _ & Hli & _ & Hmir & _).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  pose proof (R_regions_sep _ _ _ _ _ HR) as Hsep.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hgp) as Hregp.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hg) as Hregt.
  destruct HS as [_ _ Hsp _].
  pose proof (u64 (rho p)) as Hrp.
  (* [comment removed for export] *)
  assert (Hal8 : bv_unsigned (rho p) mod 8 = 0).
  { destruct Hregp as (_ & _ & _ & _ & Hal & _). exact (mod8_of_align _ _ Halp Hal). }
  set (x := 8 * (y - to_Z shadow_K)).
  assert (Hx : bv_unsigned (rho p) <= x /\ x + 8 <= bv_unsigned (rho p) + to_Z (rg_len rgp)).
  { unfold x. rewrite K_val in *. clear - Hal8 Hy1 Hy2 Hrp. Z.div_mod_to_equations. lia. }
  assert (Hyspan : in_span y).
  { unfold in_span, span_lo, span_hi in *. rewrite K_val in *. clear - Hal8 Hy1 Hy2 Hrp H47 Hmiss.
    Z.div_mod_to_equations. lia. }
  pose proof (Hsp t rg Hg) as Hok. unfold span_ok in Hok. unfold in_ival in Hin.
  destruct (rg_kind rg) as [|q] eqn:Ek.
  - destruct Hok as [Hm | (_ & _ & Hpre)].
    + unfold in_span in Hyspan. lia.
    + destruct (Hpre y Hin) as (p0 & Hp0 & Hl & Hh). fold x in Hl, Hh.
      (* [comment removed for export] *)
      destruct Hmir as (Hm1 & _).
      pose proof (proj1 (Forall_forall _ _) Hm1 _ Hwhole) as (rg' & Hg' & _ & _ & Hi).
      rewrite to_Z_0, adr_0 in Hi.
      pose proof (proj1 (Forall_forall _ _) (li_disj_R _ _ _ _ _ Hli) _ Hi) as HdR.
      pose proof (proj1 (Forall_forall _ _) HdR p0 Hp0) as Hd.
      pose proof (i63_range (rg_len rgp)) as Hlr.
      unfold e_disj, e_hi, e_lo, e_sz in Hd, Hl, Hh. cbn [fst snd] in Hd.
      rewrite u64_lit in Hd by lia. lia.
  - destruct Hok as (Et & rgq & Hgq & Halq & Hloq & Hlenq).
    destruct Hregt as (_ & _ & _ & _ & _ & _ & Hkind). rewrite Ek in Hkind. cbn [rkind_ok] in Hkind.
    destruct Hkind as [_ Hbase].
    pose proof (R_region_ok _ _ _ _ _ _ _ HR Hgq) as Hregq.
    assert (Hal8q : bv_unsigned (rho q) mod 8 = 0).
    { destruct Hregq as (_ & _ & _ & _ & Hal & _). exact (mod8_of_align _ _ Halq Hal). }
    assert (Hxq : in_ival rho q rgq x).
    { unfold in_ival, x. rewrite Hbase in Hin. rewrite K_val in *. pose proof (u64 (rho q)) as Hrq.
      clear - Hin Hal8q Hloq Hlenq Hrq. Z.div_mod_to_equations. lia. }
    assert (Hxp : in_ival rho p rgp x) by (unfold in_ival; lia).
    destruct (Uint63.eqb q p) eqn:E.
    + apply Uint63.eqb_spec in E. subst q. rewrite Et in Hg. rewrite Hfresh in Hg. discriminate.
    + apply eqb_false_spec in E. exact (ival_disjoint R0 rho (f_mem F) q p rgq rgp x Hsep E Hgq Hgp Hxq Hxp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DInv3_add_shadow n1 rho F L3 ms m p rgp sl :
  D3 n1 rho F L3 ms m ->
  iget p (f_mem F) = Some rgp -> n1 = (p + 1)%uint63 -> to_Z p < to_Z n1 ->
  0 < to_Z n1 -> to_Z n1 < 2 ^ 60 - 1 -> regions_lt n1 (f_mem F) ->
  to_Z (rg_lo rgp) = 0 -> to_Z (rg_align rgp) = 12 ->
  8 * to_Z sl = to_Z (rg_len rgp) -> 0 < to_Z sl ->
  (bv_unsigned (rho p) + to_Z (rg_len rgp) <= span_lo \/ span_hi <= bv_unsigned (rho p)) ->
  bv_unsigned (rho p) + to_Z (rg_len rgp) <= 2 ^ 47 ->
  In (p, 0%uint63, rg_len rgp) (fl_maps (fl3 L3)) ->
  (forall e, In e (fl_ex L3) -> fent_tag e <> p) ->
  let L3' := shadow_ledger3 L3 n1 sl in
  acct_ok Lim L3' = true ->
  D3 (n1 + 1)%uint63 (rho_upd rho n1 (sh_base (rho p))) (add_region F n1 (shadow_region sl p)) L3' ms m
  /\ mfr IM rho F L3 ms (n1 + 1)%uint63 (rho_upd rho n1 (sh_base (rho p))) (add_region F n1 (shadow_region sl p)) L3' ms.
Proof.
  intros HD Hgp En1 Hpn1 Hn0 Hn60 Hlt Hlo0 Hal12 Hsl Hslpos Hmiss H47 Hwhole Hexp L3' Hacct.
  pose proof HD as (HDI & HL & HS & HX).
  pose proof HDI as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hgp) as Hregp.
  pose proof (u64 (rho p)) as Hrp. pose proof (i63_range sl) as Hslr.
  set (SB := bv_unsigned (rho p) / 8 + to_Z shadow_K).
  set (sb := sh_base (rho p)). set (rho2 := rho_upd rho n1 sb).
  set (M2 := iset n1 (shadow_region sl p) (f_mem F)).
  assert (Hal4096 : bv_unsigned (rho p) mod 4096 = 0).
  { destruct Hregp as (_ & _ & _ & _ & Hal & _). rewrite Hal12 in Hal. exact Hal. }
  assert (HSBlo : lsh_lo <= SB /\ SB + to_Z sl <= hsh_hi /\ SB mod 512 = 0
                  /\ 8 * SB = bv_unsigned (rho p) + 8 * to_Z shadow_K).
  { unfold SB, lsh_lo, hsh_hi. rewrite K_val. clear - Hal4096 Hrp H47 Hsl Hslr. Z.div_mod_to_equations. lia. }
  destruct HSBlo as (HSB1 & HSB2 & HSB3 & HSB4).
  assert (Hsbu : bv_unsigned sb = SB).
  { unfold sb, sh_base. fold SB. apply u64_lit. unfold lsh_lo, hsh_hi in *. lia. }
  assert (Hfresh : iget n1 (f_mem F) = None) by (apply fxs_fresh_none; exact Hlt).
  assert (Hfresh' : iget (p + 1)%uint63 (f_mem F) = None) by (rewrite <- En1; exact Hfresh).
  assert (Hrho2 : forall t, to_Z t < to_Z n1 -> rho2 t = rho t).
  { intros t Ht. unfold rho2. apply rho_upd_other. apply (lt_neq R0). exact Ht. }
  assert (Hrn1 : rho2 n1 = sb) by (unfold rho2; apply rho_upd_same).
  assert (Hn1s : to_Z (n1 + 1)%uint63 = to_Z n1 + 1) by (apply (to_Z_succ61 R0); lia).
  assert (Hreg_old : forall t rg, iget t (f_mem F) = Some rg -> rho2 t = rho t /\ iget t M2 = Some rg /\ t <> n1).
  { intros t rg Hg. pose proof (Hlt t rg Hg) as Htn. split; [exact (Hrho2 t Htn)|].
    assert (Hne : t <> n1) by (intros ->; lia). split; [|exact Hne].
    unfold M2. rewrite iget_iset_other; [exact Hg|]. intros E. apply Hne. symmetry. exact E. }
  (* [comment removed for export] *)
  assert (Hsep : forall y, SB <= y < SB + to_Z sl -> no_region rho (f_mem F) y).
  { intros y Hy t rg Hg Hin.
    apply (shadow_sep_all n1 rho F L3 ms m p rgp y t rg HD Hgp Hfresh' Hlo0 ltac:(lia) Hmiss H47 Hwhole);
      fold SB; try assumption; lia. }
  assert (Hspan_in : forall y, SB <= y < SB + to_Z sl -> in_span y).
  { intros y Hy. unfold in_span, span_lo, span_hi, lsh_lo, hsh_hi in *. lia. }
  assert (Hsep_iv : forall t rg, iget t (f_mem F) = Some rg ->
            SB + to_Z sl <= bv_unsigned (rho t) + to_Z (rg_lo rg)
            \/ bv_unsigned (rho t) + to_Z (rg_len rg) <= SB).
  { intros t rg Hg. destruct (Hcov t rg Hg) as [Hne _].
    destruct (Z_le_gt_dec (SB + to_Z sl) (bv_unsigned (rho t) + to_Z (rg_lo rg))) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (bv_unsigned (rho t) + to_Z (rg_len rg)) SB) as [H2|H2]; [right; exact H2|].
    exfalso. apply (Hsep (Z.max SB (bv_unsigned (rho t) + to_Z (rg_lo rg))) ltac:(lia) t rg Hg).
    unfold in_ival. lia. }
  destruct HS as [Hz Hspcov Hsp Hexc].
  destruct HL as [Hpi Hreg Hpw Hml Hsub HAb Hlim Hex Hexna Hexlz H9a H9b Htags HE Hacc Hwfna Hwflz HopsR Hord Hopsf Hres].
  apply Forall_app in Htags as [Ht1 Htags]. apply Forall_app in Htags as [Ht2 Ht3].
  destruct (stable_den rho rho2 n1 _ Hrho2 Ht1) as [Eall _].
  destruct (stable_den rho rho2 n1 _ Hrho2 Ht3) as [_ EA].
  pose proof (lazy_cov_tags _ _ n1 Hsub Ht1) as Ht4.
  pose proof (lazy_cov_tags _ _ n1 Hexc Ht1) as Ht5.
  assert (Hden_lt : forall e0 : fent, to_Z (fent_tag e0) < to_Z n1 -> den rho2 e0 = den rho e0).
  { intros [[t0 o0] l0] Ht0. cbn [fent_tag fst] in Ht0. cbn [den]. unfold adr. rewrite (Hrho2 t0 Ht0). reflexivity. }
  destruct (ops_apply_ext rho rho2 (fl_ops L3)) as [Eops_na Eops_lz].
  { intros o Ho. apply Hden_lt. apply (proj1 (Forall_forall _ _) Ht2). apply in_map. exact Ho. }
  assert (Hden0 : forall e0 : fent, fent_tag e0 = 0%uint63 -> den rho2 e0 = den rho e0).
  { intros e0 Et0. apply Hden_lt. rewrite Et0, to_Z_0. lia. }
  (* [comment removed for export] *)
  assert (Hshadow_in : forall y, SB <= y < SB + to_Z sl -> in_shadow y).
  { intros y Hy. unfold in_shadow. destruct Hmiss as [Hlow | Hhigh]; [left | right].
    - unfold lsh_lo, lsh_hi, span_lo in *. rewrite K_val in *.
      clear - HSB1 HSB4 Hsl Hlow Hrp Hslr Hy. lia.
    - unfold hsh_lo, hsh_hi, span_hi in *. rewrite K_val in *.
      clear - HSB2 HSB4 Hsl Hhigh Hrp Hslr Hy. lia. }
  (* [comment removed for export] *)
  assert (Hnex_in : forall y, SB <= y < SB + to_Z sl -> ~ exempted rho (fl_ex L3) y).
  { intros y Hy (e & z & He & Hz' & Ey).
    pose proof (li_top _ _ _ _ _ Hli) as Htopm. pose proof (li_disj _ _ _ _ _ Hli) as Hpw0.
    change (vm_maps (m_vmmaps (erase m))) with (vm_maps (m_vmmaps m)) in Htopm, Hpw0.
    change (alloc_top (m_vmmaps (erase m))) with (alloc_top (m_vmmaps m)) in Htopm.
    pose proof (alloc_top_lt (m_vmmaps m)) as Hattop. unfold two_pow_64 in Hattop.
    destruct (lazy_cov_inside rho (fl_all L3) (fl_ex L3) (vm_maps (m_vmmaps m)) e Hexc Hex) as (e' & He' & Et' & Hins);
      [|exact He|].
    { intros q Hq. pose proof (proj1 (Forall_forall _ _) Htopm q Hq) as [_ Hh0]. lia. }
    set (ep := (p, 0%uint63, rg_len rgp)).
    assert (Hepall : In ep (fl_all L3)) by (exact (proj1 (Forall_forall _ _) H9a ep Hwhole)).
    assert (Hneq : e' <> ep).
    { intros E. apply (Hexp e He). rewrite <- Et', E. reflexivity. }
    rewrite Hex in Hpw0.
    pose proof (pw_disj_map_In (den rho) _ e' ep Hpw0 He' Hepall Hneq) as Hd.
    assert (Hdenp : den rho ep = (rho p, Z_to_bv 64 (to_Z (rg_len rgp)))).
    { unfold ep. cbn [den]. rewrite to_Z_0, adr_0. reflexivity. }
    rewrite Hdenp in Hd. pose proof (i63_range (rg_len rgp)) as Hlr.
    unfold e_disj, e_inside, e_hi, e_lo, e_sz in Hd, Hins, Hz'. cbn [fst snd] in Hd.
    rewrite u64_lit in Hd by lia.
    assert (Hzp : bv_unsigned (rho p) <= z < bv_unsigned (rho p) + to_Z (rg_len rgp)).
    { unfold SB in Hy. rewrite K_val in *. clear - Hy Ey Hal4096 Hsl Hrp. Z.div_mod_to_equations. lia. }
    unfold e_lo, e_sz in *. lia. }
  assert (HRn2 : Rn (n1 + 1)%uint63 rho2 (add_region F n1 (shadow_region sl p)) ms).
    { intros rho'' Hag. destruct (agree_upd n1 rho sb rho'' ltac:(lia) Hag) as [Hag0 Hn1].
      pose proof (HRn rho'' Hag0) as HR''. destruct HR'' as [P1 P2 P3 P4 P5].
      constructor; cbn [add_region f_pc f_regs f_mem f_resv]; try assumption.
      assert (Hold : forall t rg, iget t (f_mem F) = Some rg -> rho'' t = rho t).
      { intros t rg Hg. exact (proj2 Hag0 t (Hlt t rg Hg)). }
      apply mem_ok_add_region; [exact P5 | exact Hfresh | | |].
      + unfold region_ok, shadow_region. cbn [rg_len rg_lo rg_align rg_clo rg_chi rg_kind rkind_ok].
        rewrite Hn1, Hsbu, (proj2 Hag0 p Hpn1).
        change (to_Z 9) with 9. change (2 ^ 9) with 512. change (to_Z 0) with 0.
        change (to_Z clo_dflt) with 0. change (to_Z chi_dflt) with (2 ^ 63 - 1).
        destruct Hregp as (_ & Hl62 & _). unfold lsh_lo, hsh_hi in *.
        repeat split; first [lia | exact HSB3].
      + intros t' rg' Hg'. rewrite Hn1, Hsbu, (Hold t' rg' Hg'). unfold shadow_region. cbn [rg_lo rg_len].
        change (to_Z 0) with 0. destruct (Hsep_iv t' rg' Hg'); [left | right]; lia.
      + intros pn p0 Hpn Hpa. unfold page_at in Hpa. cbn [shadow_region rg_pages rg_dflt] in Hpa.
        rewrite iget_iempty in Hpa.
        rewrite (fxs_eqb_false n1 0%uint63) in Hpa by (change (to_Z 0) with 0; lia).
        destruct (page_in_region (shadow_region sl p) pn) eqn:Epr; [| discriminate Hpa].
        inversion Hpa; subst p0. clear Hpa.
        destruct (fxs_page_in_region_spec _ pn Hpn Epr) as (Hplo & Hpup & Hpal & _).
        pose proof (to_Z_bounded pn) as Hpnb.
        split; [| split; [exact Hplo | split; [exact Hpup | exact Hpal]]].
        apply page_ok_zero_v; [exact (proj1 Hag)|].
        intros j Hj.
        destruct (fxs_clim_bytes _ pn j Hj) as [Hjl Hj4]. unfold shadow_region in Hjl. cbn [rg_len] in Hjl.
        assert (Ea : bv_unsigned (adr rho'' n1 (to_Z pn * 4096 + j)) = SB + (to_Z pn * 4096 + j)).
        { pose proof (i63_range pn). rewrite fxs_adr_unsigned; rewrite ?Hn1, ?Hsbu; unfold hsh_hi in *; lia. }
        apply Hz; rewrite Ea; [apply Hshadow_in | apply Hsep | apply Hnex_in]; lia. }
  assert (H02 : rho2 0%uint63 = Z_to_bv 64 0).
  { unfold rho2. rewrite rho_upd_other; [exact H0|]. intros E. rewrite <- E, to_Z_0 in Hn0. lia. }
  assert (Hmem2 : mem_ok segs IM rho2 M2 (ms_mem ms)).
  { exact (R_mem _ _ _ _ _ (Rn_R _ _ _ _ _ _ HRn2 H02)). }
  assert (Hrange_s : e_lo (den rho2 (n1, 0%uint63, sl)) = SB /\ e_hi (den rho2 (n1, 0%uint63, sl)) = SB + to_Z sl).
  { unfold e_hi, e_lo, e_sz. cbn [den fst snd]. rewrite to_Z_0, adr_0, Hrn1, Hsbu, u64_lit by lia. split; reflexivity. }
  split.
  2:{ (* [comment removed for export] *)
      exists [(OpShadow, (n1, 0%uint63, sl))]. split; [reflexivity|].
      split; [constructor; [cbn [snd fent_tag fst]; lia | constructor]|].
      split; [intros; reflexivity|]. split.
      2:{ intros x (t & rg & pn & p0 & ci & Hg & Hp & Hci & j & Hj & ->). left.
          destruct (Hreg_old t rg Hg) as (Er & Eg & _). exists t, rg, pn, p0, ci.
          cbn [add_region f_mem]. fold M2. split; [exact Eg|]. split; [exact Hp|]. split; [exact Hci|].
          exists j. split; [exact Hj|]. unfold adr. rewrite Er. reflexivity. }
      intros x (t & rg & pn & p0 & j & Hg & Hpn & Hp & Hw & Hj & Hjl & ->).
      cbn [add_region f_mem] in Hg. fold M2 in Hg.
      destruct (t =? n1)%uint63 eqn:E.
      - apply Uint63.eqb_spec in E. subst t. right. exists (OpShadow, (n1, 0%uint63, sl)). split; [left; reflexivity|].
        cbn [snd]. rewrite (proj1 Hrange_s), (proj2 Hrange_s).
        unfold M2 in Hg. rewrite iget_iset_same in Hg. injection Hg as <-.
        unfold shadow_region in Hjl. cbn [rg_len] in Hjl.
        pose proof (i63_range pn) as Hpn0.
        rewrite adr_unsigned by (rewrite ?Hrn1, ?Hsbu; unfold hsh_hi in *; lia). rewrite Hrn1, Hsbu. lia.
      - unfold M2 in Hg. rewrite iget_iset_other in Hg by (intros E'; rewrite E', Uint63.eqb_refl in E; discriminate).
        left. exists t, rg, pn, p0, j. repeat (split; [assumption|]).
        unfold adr. rewrite (proj1 (Hreg_old t rg Hg)). reflexivity. }
  split; [|split; [|split]].
  - (* [comment removed for export] *)
    split; [exact HRn2|].
    split; [exact H02|].
    split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
    split.
    { (* [comment removed for export] *)
      intros t rg Hg. cbn [add_region f_mem] in Hg. fold M2 in Hg. unfold M2 in Hg. rewrite iget_iset in Hg.
      destruct (t =? n1)%uint63 eqn:E.
      - apply Uint63.eqb_spec in E. subst t. injection Hg as <-. unfold shadow_region. cbn [rg_lo rg_len].
        change (to_Z 0) with 0. split; [lia|]. intros x Hx. unfold in_ival in Hx. cbn [rg_lo rg_len] in Hx.
        change (to_Z 0) with 0 in Hx. rewrite Hrn1, Hsbu in Hx.
        destruct (Hspcov x (Hspan_in x ltac:(lia))) as (e0 & He0 & _ & Hpx).
        left. exists (den rho e0). split; [|exact Hpx]. apply in_app_iff. right.
        change (vm_maps (m_vmmaps (erase m))) with (vm_maps (m_vmmaps m)). rewrite Hex. apply in_map. exact He0.
      - destruct (Hcov t rg Hg) as [Hne Hb]. split; [exact Hne|]. intros x Hx. apply Hb.
        assert (Htn : to_Z t < to_Z n1) by (exact (Hlt t rg Hg)).
        exact (in_ival_rho rho rho2 t rg x (Hrho2 t Htn) Hx). }
    split.
    { (* [comment removed for export] *)
      destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). cbn [add_region f_mem]. fold M2. split; [|split].
      - eapply Forall_impl; [|exact Hm1]. intros e He.
        destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hreg_old _ _ Hrg) as (Er & Eg & _).
        apply (ent_ok_ext rho rho2 (f_mem F) M2 (vm_maps (m_vmmaps (erase m))) (vm_maps (m_vmmaps (erase m))) e Er);
          [rewrite Eg, Hrg; reflexivity | intros q Hq; exact Hq | exact He].
      - eapply Forall_impl; [|exact Hm2]. intros e He.
        destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hreg_old _ _ Hrg) as (Er & Eg & _).
        apply (ent_ok_ext rho rho2 (f_mem F) M2 (vm_noaccess (m_vmmaps (erase m))) (vm_noaccess (m_vmmaps (erase m))) e Er);
          [rewrite Eg, Hrg; reflexivity | intros q Hq; exact Hq | exact He].
      - destruct (Hreg_old _ _ Hgb) as (Er & Eg & _). exists rgb. split; [exact Eg|].
        rewrite (adr_rho rho rho2 _ _ Er). exact Hbrk. }
    split; [exact I|].
    split.
    { apply (XI_rho rho rho2); [|exact HXI]. intros tx Htx. exact (Hrho2 tx (Hxt tx Htx)). }
    split; [intros tx Htx; rewrite Hn1s; pose proof (Hxt tx Htx); lia|].
    intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem].
    destruct Hpr as (Hne0 & rgt & Hgt & Hpr2). destruct (Hreg_old _ _ Hgt) as (Er & Eg & _).
    cbn [add_region f_mem]. fold M2.
    split; [split; [exact Hne0 | exists rgt; split; [exact Eg | exact Hpr2]]|].
    intros rg x Hgx Hx. rewrite Eg in Hgx. injection Hgx as <-.
    exact (Hmem rgt x Hgt (in_ival_rho rho rho2 t rgt _ Er Hx)).
  - (* [comment removed for export] *)
    apply Z.leb_le in Hacct. unfold acct_ok in Hacct. cbn [L3' shadow_ledger3 fl_E fl_Ab] in Hacct.
    set (iv := denA rho2 (n1, 0%uint63, sl)).
    assert (Hiv : iv = (pg_dn SB, pg_upZ (SB + to_Z sl))).
    { unfold iv. cbn [denA]. rewrite Hrn1, Hsbu. change (to_Z 0) with 0. rewrite Z.add_0_r. reflexivity. }
    pose proof (denA_width rho2 (n1, 0%uint63, sl)) as Hw.
    fold iv in Hw. cbn [snd] in Hw.
    constructor; unfold FxDrive3.allowed; cbn [L3' shadow_ledger3 fl3 fl_all fl_ops fl_lazy fl_allow fl_Ab fl_E fl_ex map]; fold iv.
    + destruct Hpi as [P1 P2 P3 P4]. constructor; try assumption.
      * eapply Forall_impl; [|exact P3]. intros q Hq. rewrite EA.
        apply page_allowedb_cons. exact Hq.
      * cbn [A_bytes fold_right app]. fold (A_bytes (map (denA rho2) (fl_allow L3) ++ A0)). rewrite EA.
        unfold FxDrive3.allowed in HAb. clear - HE HAb Hacct Hw Hlim. unfold fent in *. lia.   (* [comment removed for export] *)
    + cbn [add_region f_mem]. fold M2.
      apply (LZ_build segs IM rho rho2 (m_vm_lazy m) (m_vm_lazy m) (map (denA rho) (fl_allow L3) ++ A0)
               ((iv :: map (denA rho2) (fl_allow L3)) ++ A0) (f_mem F) M2 (ms_mem ms) Hmem2 Hreg).
      * intros pb Hpb. rewrite EA. apply page_allowedb_cons. exact Hpb.
      * intros t rg Hg. unfold M2 in Hg. rewrite iget_iset in Hg.
        destruct (t =? n1)%uint63 eqn:E.
        -- apply Uint63.eqb_spec in E. subst t. injection Hg as <-. left. right. exists iv. split; [left; reflexivity|].
           rewrite Hiv. cbn [fst snd shadow_region rg_lo rg_len]. change (to_Z 0) with 0. rewrite Hrn1, Hsbu.
           split; [apply pg_dn_mod|]. split; [apply pg_upZ_mod|].
           pose proof (pg_dn_le SB). pose proof (pg_upZ_ge (SB + to_Z sl)). lia.
        -- right. assert (Htn : to_Z t < to_Z n1) by (exact (Hlt t rg Hg)).
           split; [exact Hg|]. split; [exact (Hrho2 t Htn)|]. intros z _ Hpg. exact Hpg.
    + intros e0 q He0 Hq H1 H2. rewrite (Hden_lt e0 (proj1 (Forall_forall _ _) Ht4 e0 He0)) in H1, H2.
      exact (Hpw e0 q He0 Hq H1 H2).
    + exact Hml.
    + exact Hsub.
    + cbn [A_bytes fold_right app]. fold (A_bytes (map (denA rho2) (fl_allow L3) ++ A0)). rewrite EA.
      unfold FxDrive3.allowed in HAb. clear - HAb Hw. lia.
    + exact Hlim.
    + rewrite Hex, Eall; reflexivity.
    + rewrite Hexna, na_apply_snoc. unfold na_step. cbn [fst]. symmetry. apply Eops_na.
    + rewrite Hexlz, lz_apply_snoc. unfold lz_step. cbn [fst]. symmetry. apply Eops_lz.
    + exact H9a.
    + apply Forall_forall. intros e0 He0in.
      destruct (proj1 (Forall_forall _ _) H9b e0 He0in) as [He0|[He0|He0]]; [left; exact He0 | right; left; exact He0 |].
      right; right. cbn [add_region f_mem]. rewrite iget_iset_other; [exact He0|]. intros E.
      pose proof (proj1 (Forall_forall _ _) Ht1 e0 He0in) as Hlt0. rewrite E in Hlt0. lia.
    + rewrite !Forall_app. rewrite Hn1s. split; [|split].
      * eapply Forall_impl; [|exact Ht1]. cbv beta. intros; lia.
      * rewrite map_app, Forall_app. split; [eapply Forall_impl; [|exact Ht2]; cbv beta; intros; lia|].
        constructor; [cbn [snd fent_tag fst]; lia | constructor].
      * constructor; [cbn [fent_tag fst]; lia|]. eapply Forall_impl; [|exact Ht3]. cbv beta. intros; lia.
    + exact HE.
    + exact Hacct.
    + exact Hwfna.
    + exact Hwflz.
    + intros o x q Ho Hq Hx. apply in_app_iff in Ho as [Ho | [<- | []]].
      * rewrite (Hden_lt (snd o)) in Hx by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
        exact (HopsR o x q Ho Hq Hx).
      * cbn [snd] in Hx. rewrite (proj1 Hrange_s), (proj2 Hrange_s) in Hx. intros Hxq.
        destruct (Hspcov x (in_shadow_span x (Hshadow_in x Hx))) as (e0 & He0 & _ & Hpx).
        assert (Hin0 : In (den rho e0) (vm_maps (m_vmmaps m))) by (rewrite Hex; apply in_map; exact He0).
        pose proof (li_disj_R _ _ _ _ _ Hli) as HdR.
        change (vm_maps (m_vmmaps (erase m))) with (vm_maps (m_vmmaps m)) in HdR.
        pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) HdR _ Hin0) q Hq) as Hd.
        unfold e_disj in Hd. lia.
    + (* [comment removed for export] *)
      apply (ords_ok_ext n1 rho); [rewrite Hn1s; lia | exact Hrho2 | exact Hord].
    + (* [comment removed for export] *)
      rewrite Forall_app. split.
      * apply Forall_forall. intros o Ho.
        assert (Hto : to_Z (fent_tag (snd o)) < to_Z n1)
          by (apply (proj1 (Forall_forall _ _) Ht2); apply in_map; exact Ho).
        apply (op_ok_ext n1 rho rho2 m m (fl_all L3) (fl_all L3) o Hrho2 Hto Ht1 eq_refl (fun e' He' _ => He')).
        exact (proj1 (Forall_forall _ _) Hopsf o Ho).
      * constructor; [|constructor]. unfold op_ok. cbn [fst snd fent_tag]. cbv zeta.
        split; [lia|]. split.
        -- assert (Ep : (n1 - 1)%uint63 = p).
           { rewrite En1. apply to_Z_inj. pose proof (i63_range p) as Hp0.
             assert (Hp1 : to_Z (p + 1)%uint63 = to_Z p + 1) by (apply (to_Z_succ61 R0); lia).
             rewrite sub_spec, Hp1, to_Z_1, i63_wB. rewrite Z.mod_small by lia. lia. }
           rewrite Ep, Hrn1, Hsbu, (Hrho2 p) by lia. reflexivity.
        -- intros x Hx. rewrite (proj1 Hrange_s), (proj2 Hrange_s) in Hx. exact (Hspan_in x Hx).
    + (* [comment removed for export] *)
      apply (ress_ok_ext n1 rho); [rewrite Hn1s; lia | exact Hrho2 | exact Hres].
  - (* [comment removed for export] *)
    constructor; cbn [L3' shadow_ledger3 fl_all fl_ex].
    + intros x Hx Hno Hnex. apply (Hz x Hx).
      * intros t rg Hg Hin.
        destruct (Hreg_old t rg Hg) as (Er & Eg & _). apply (Hno t rg Eg).
        unfold in_ival in *. rewrite Er. exact Hin.
      * intros Hc. apply Hnex. apply (exempted_ext rho rho2); [|exact Hc].
        intros e0 He0. exact (Hden_lt e0 (proj1 (Forall_forall _ _) Ht5 e0 He0)).
    + intros x Hx. destruct (Hspcov x Hx) as (e0 & He0 & Et0 & Hpx). exists e0.
      split; [exact He0|]. split; [exact Et0|]. rewrite (Hden0 e0 Et0). exact Hpx.
    + intros t rg Hg. cbn [add_region f_mem] in Hg. fold M2 in Hg. unfold M2 in Hg. rewrite iget_iset in Hg.
      cbn [add_region f_mem]. fold M2.
      destruct (t =? n1)%uint63 eqn:E.
      * apply Uint63.eqb_spec in E. subst t. injection Hg as <-. unfold span_ok, shadow_region. cbn [rg_kind rg_lo rg_len].
        split; [exact En1|]. exists rgp. destruct (Hreg_old p rgp Hgp) as (_ & Eg & _).
        change (to_Z 0) with 0. split; [exact Eg|]. split; [lia|]. split; lia.
      * destruct (Hreg_old t rg Hg) as (Er & _ & _). pose proof (Hsp t rg Hg) as Hok. unfold span_ok in *.
        destruct (rg_kind rg) as [|q]; [rewrite Er; exact Hok|].
        destruct Hok as (Et & rgq & Hgq & Hrest). split; [exact Et|]. exists rgq.
        split; [exact (proj1 (proj2 (Hreg_old q rgq Hgq))) | exact Hrest].
    + exact Hexc.
  - (* [comment removed for export] *)
    destruct HX as (X1 & X2 & X3 & X4 & X5). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    split; [|exact X5].
    intros x Hx. destruct (X4 x Hx) as (Ht & Hno & Hm). split; [exact Ht|]. split; [|exact Hm].
    intros t rg Hg Hin. cbn [add_region f_mem] in Hg. fold M2 in Hg. unfold M2 in Hg. rewrite iget_iset in Hg.
    destruct (t =? n1)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst t. injection Hg as <-. unfold in_ival, shadow_region in Hin.
      cbn [rg_lo rg_len] in Hin. rewrite Hrn1, Hsbu in Hin.
      destruct (ledger_inv_alloc_top _ _ _ _ _ Hli) as [Hlo _].
      change (alloc_top (m_vmmaps (erase m))) with (alloc_top (m_vmmaps m)) in Hlo.
      rewrite alloc_lo_bound_val in Hlo. unfold hsh_hi in *. lia.
    + assert (Htn : to_Z t < to_Z n1) by (exact (Hlt t rg Hg)).
      apply (Hno t rg Hg). exact (in_ival_rho rho rho2 t rg _ (Hrho2 t Htn) Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable shp : int -> bool.

Local Abbreviation SOK := (sys_ok3 cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0).

Theorem sys_grant3p_sound n rho F L3 ms m nr len res :
  sys_grant3p Rb Rc Lim shp nr F L3 n len = Some res ->
  D3 n rho F L3 ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = (if nr then 16418 else 34) ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  SOK n rho F L3 res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5. unfold sys_grant3p in Hsys.
  destruct (sys_grant3 Rb Rc Lim nr F L3 n len) as [[F1 L31 n1|]|] eqn:Hg3; try discriminate.
  destruct (shp (pg_up len)) eqn:Hshp.
  2:{ injection Hsys as <-.
      exact (sys_grant3_sound cfg segs IM Halloc R0 Rb Rc Lim HRb HRc keep mem0 XI xtags XI_rho XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
               n rho F L3 ms m nr len _ Hg3 HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5). }
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  injection Hsys as <-. apply andb_true_iff in Hchk as [Hn1 Hacct2].
  apply ltb_spec in Hn1. change (to_Z 1152921504606846975) with (2 ^ 60 - 1) in Hn1.
  destruct (sys_grant3_inv Rb Rc Lim nr F L3 n len _ Hg3) as (Hpos & Hle & Hup & Htag & _ & _).
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec R0 len Hle) as HnZ.
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt].
  apply andb_true_iff in Htag as [Hn0 Hn60]. apply ltb_spec in Hn0, Hn60. rewrite to_Z_0 in Hn0.
  change (to_Z 1152921504606846976) with (2 ^ 60) in Hn60.
  apply regions_lt_b_ok in Hlt.
  pose proof (to_Z_succ61 R0 n Hn60) as Hn1s.
  destruct (grant3_steps cfg segs IM Halloc R0 Rb Rc Lim HRb HRc keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
              n rho F L3 ms m nr len _ Hg3 HD Hstep Hx8 Ha1 Ha2 Ha3 Ha5) as (I & i0 & aof & Hiff & Hadm).
  set (nZ := page_round_up_Z (to_Z len)) in *. set (nZi := pg_up len) in *.
  exists I, i0, (fun i => mkCfg (sysret (ms_pend ms) (aof i) (apply_zeros (ms_mem (ms_pend ms)) [(aof i, Z_to_bv 64 nZ)]))
                         (grant_model3 nr (aof i) nZ m)).
  split; [exact Hiff|].
  intros i. cbn [cfg_ms cfg_model]. set (a := aof i).
  destruct (grant3_succ cfg segs IM R0 Rb Rc Lim keep mem0 XI xtags XI_rho XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
              n rho F L3 ms m nr len _ a Hg3 HD Hat (Hadm i)) as (L3' & E & HD' & Hdx & EL & Hmiss).
  cbv zeta in HD', Hdx, Hmiss. fold nZ nZi in HD', Hdx, Hmiss, EL.
  injection E as EF EL3 En1. subst F1 L31 n1.
  set (rho1 := rho_upd rho n a) in *.
  set (ms' := sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 nZ)])) in *.
  set (m' := grant_model3 nr a nZ m) in *.
  set (sl := (nZi >> 3)%uint63) in *.
  set (rgp := RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)).
  assert (Hrn : rho1 n = a) by (unfold rho1; apply rho_upd_same).
  assert (HnZmod : nZ mod 4096 = 0) by (apply page_round_up_Z_mod).
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  assert (Hsl : 8 * to_Z sl = to_Z nZi /\ 0 < to_Z sl).
  { unfold sl. rewrite lsr_spec. change (2 ^ to_Z 3) with 8. rewrite HnZ.
    clear - HnZmod HnZpos. Z.div_mod_to_equations. lia. }
  pose proof (Hadm i) as Hadmi. fold a in Hadmi. apply mmap_grant_na_b_iff in Hadmi as (_ & _ & Hatop & _).
  pose proof HD as ((_ & _ & _ & _ & Hli & _) & _).
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hli) as [_ Htop]. unfold TASK_SIZE in Htop.
  change (alloc_top (m_vmmaps (erase m))) with (alloc_top (m_vmmaps m)) in Htop.
  assert (HD2 : D3 (n + 1 + 1)%uint63 (rho_upd rho1 (n + 1)%uint63 (sh_base (rho1 n)))
                   (add_region (fx_grant F n nZi) (n + 1)%uint63 (shadow_region sl n))
                   (shadow_ledger3 L3' (n + 1)%uint63 sl) ms' m'
                /\ mfr IM rho1 (fx_grant F n nZi) L3' ms' (n + 1 + 1)%uint63 (rho_upd rho1 (n + 1)%uint63 (sh_base (rho1 n)))
                       (add_region (fx_grant F n nZi) (n + 1)%uint63 (shadow_region sl n))
                       (shadow_ledger3 L3' (n + 1)%uint63 sl) ms').
  { apply (DInv3_add_shadow (n + 1)%uint63 rho1 (fx_grant F n nZi) L3' ms' m' n rgp sl HD').
    - change (f_mem (fx_grant F n nZi)) with (iset n rgp (f_mem F)). apply iget_iset_same.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros t rg Hg. change (f_mem (fx_grant F n nZi)) with (iset n rgp (f_mem F)) in Hg.
      rewrite iget_iset in Hg. destruct (t =? n)%uint63 eqn:Et.
      + apply Uint63.eqb_spec in Et. subst t. lia.
      + pose proof (Hlt t rg Hg). lia.
    - reflexivity.
    - reflexivity.
    - unfold rgp. cbn [rg_len]. exact (proj1 Hsl).
    - exact (proj2 Hsl).
    - unfold rgp. cbn [rg_len]. rewrite Hrn, HnZ. exact Hmiss.
    - unfold rgp. cbn [rg_len]. rewrite Hrn, HnZ. lia.
    - unfold rgp. cbn [rg_len]. rewrite EL. destruct nr; cbn [grant_ledger3 fl3 fl_maps]; left; reflexivity.
    - intros e He. rewrite EL in He. cbn [grant_ledger3 fl_ex] in He.
      destruct HD as (_ & HL0 & HS0 & _).
      pose proof (lp_tags _ _ _ _ _ _ _ _ _ _ _ HL0) as Htg. apply Forall_app in Htg as [Htg _].
      pose proof (proj1 (Forall_forall _ _) (lazy_cov_tags _ _ n (sp_ex _ _ _ _ _ _ HS0) Htg) e He) as Hlt'.
      cbv beta in Hlt'. intros E. rewrite E in Hlt'. lia.
    - exact Hacct2. }
  exists (add_region (fx_grant F n nZi) (n + 1)%uint63 (shadow_region sl n)),
         (shadow_ledger3 L3' (n + 1)%uint63 sl), (n + 1 + 1)%uint63,
         (rho_upd rho1 (n + 1)%uint63 (sh_base (rho1 n))).
  split; [reflexivity|]. split; [exact (proj1 HD2)|].
  apply (pext_trans IM R0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hdx).
  split; [|exact (proj2 HD2)].
  split; [rewrite (to_Z_succ61 R0 (n + 1)%uint63) by lia; lia|].
  split; [intros t Ht; apply rho_upd_other; apply (lt_neq R0); exact Ht|].
  split; [apply same_but_vm_refl | repeat split; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mfr_drop_region n rho F L3 ms t1 :
  (forall rg pn, iget t1 (f_mem F) = Some rg -> iget pn (rg_pages rg) = None) ->
  mfr IM rho F L3 ms n rho (drop_region F t1) L3 ms.
Proof.
  intros Hclean. apply (mfr_same IM); [intros; reflexivity| |].
  - intros x (t & rg & pn & p & j & Hg & Hrest). exists t, rg, pn, p, j. split; [|exact Hrest].
    cbn [drop_region f_mem] in Hg. rewrite iget_iremove in Hg. destruct (t =? t1)%uint63; [discriminate | exact Hg].
  - intros x (t & rg & pn & p & ci & Hg & Hp & Hrest). exists t, rg, pn, p, ci. split; [|split; [exact Hp | exact Hrest]].
    cbn [drop_region f_mem]. rewrite iget_iremove. destruct (t =? t1)%uint63 eqn:E; [|exact Hg].
    apply Uint63.eqb_spec in E. subst t. rewrite (Hclean rg pn Hg) in Hp. discriminate.
Qed.

Lemma mfr_set_bounds n rho F L3 ms t rg clo chi :
  iget t (f_mem F) = Some rg -> mfr IM rho F L3 ms n rho (set_bounds F t rg clo chi) L3 ms.
Proof.
  intros Hg. apply (mfr_same IM); [intros; reflexivity| |].
  - intros x (t' & rg' & pn & p & j & Hg' & Hpn & Hp & Hrest).
    unfold set_bounds in Hg'. cbn [f_mem] in Hg'. rewrite iget_iset in Hg'.
    destruct (t' =? t)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst t'. injection Hg' as <-.
      exists t, rg, pn, p, j. split; [exact Hg|]. split; [exact Hpn|]. split; [exact Hp | exact Hrest].
    + exists t', rg', pn, p, j. split; [exact Hg'|]. split; [exact Hpn|]. split; [exact Hp | exact Hrest].
  - intros x (t' & rg' & pn & p & ci & Hg' & Hp & Hrest).
    destruct (t' =? t)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst t'. rewrite Hg in Hg'. injection Hg' as <-.
      exists t, (rebound rg clo chi), pn, p, ci. split; [|split; [exact Hp | exact Hrest]].
      unfold set_bounds. cbn [f_mem]. apply iget_iset_same.
    + exists t', rg', pn, p, ci. split; [|split; [exact Hp | exact Hrest]].
      unfold set_bounds. cbn [f_mem]. rewrite iget_iset, E. exact Hg'.
Qed.

Lemma mfr_snap n rho F L3 ms L t : mfr IM rho F L3 ms n rho (snap L n F t) L3 ms.
Proof.
  unfold snap. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|apply (mfr_refl IM)].
  match goal with |- context [if ?c then _ else _] => destruct c end; [|apply (mfr_refl IM)].
  exact (mfr_set_bounds n rho F L3 ms t rg _ _ Hg).
Qed.

Lemma mfr_refine3 n rho F L3 ms L t thr Fa Fb :
  refine3 L F n t thr = Some (Fa, Fb) ->
  mfr IM rho F L3 ms n rho Fa L3 ms /\ mfr IM rho F L3 ms n rho Fb L3 ms.
Proof.
  unfold refine3, refine_region. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  match goal with |- context [if ?c then _ else _] => destruct c end; [|discriminate].
  intros H. injection H as <- <-.
  split.
  - exact (mfr_trans IM rho F L3 ms n rho (set_bounds F t rg (rg_clo rg) (thr - 4096)) L3 ms n rho _ L3 ms
             (Z.le_refl _) (fun _ _ => eq_refl) (mfr_set_bounds n rho F L3 ms t rg _ _ Hg) (mfr_snap n rho _ L3 ms L t)).
  - exact (mfr_trans IM rho F L3 ms n rho (set_bounds F t rg thr (rg_chi rg)) L3 ms n rho _ L3 ms
             (Z.le_refl _) (fun _ _ => eq_refl) (mfr_set_bounds n rho F L3 ms t rg _ _ Hg) (mfr_snap n rho _ L3 ms L t)).
Qed.

(* [comment removed for export] *)
Lemma sys_ok3_pre n rho F F0 L3 res ms m :
  mfr IM rho F L3 ms n rho F0 L3 ms -> SOK n rho F0 L3 res ms m -> SOK n rho F L3 res ms m.
Proof.
  intros Hm (I & i0 & nx & Hiff & Hsucc). exists I, i0, nx. split; [exact Hiff|].
  intros i. destruct (Hsucc i) as (F' & L3' & n' & rho' & Hin & HD' & [Hdx Hmx]).
  exists F', L3', n', rho'. split; [exact Hin|]. split; [exact HD'|]. split; [exact Hdx|].
  destruct Hdx as (Hn & Hrho & _). exact (mfr_trans IM _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Hrho Hm Hmx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DInv3_drop_shadow n rho F L3 ms m t1 :
  D3 n rho F L3 ms m -> shadow_clean keep (fl3 L3) (f_mem F) t1 = true ->
  D3 n rho (drop_region F t1) L3 ms m.
Proof.
  intros (HDI & HL & HS & HX) Hcl. unfold shadow_clean in Hcl.
  destruct (iget t1 (f_mem F)) as [rg1|] eqn:Hg1; [|discriminate].
  destruct (rg_kind rg1) as [|p1] eqn:Ek1; [discriminate|].
  destruct (rg_dflt rg1) as [[| |]|] eqn:Ed1; try discriminate.
  repeat match type of Hcl with (_ && _ = true) =>
    let H := fresh "Hc" in apply andb_true_iff in Hcl as [Hcl H] end.
  rename Hcl into Hpages.
  pose proof (proj1 (iall_spec _ _) Hpages) as Hnop.
  apply Uint63.eqb_spec in Hc6.                                   (* [comment removed for export] *)
  apply Uint63.eqb_spec in Hc5. apply (f_equal to_Z) in Hc5.
  rewrite (i63_land_ones (rg_len rg1) 7%uint63 3 eq_refl ltac:(lia)) in Hc5. change (2 ^ 3) with 8 in Hc5.
  change (to_Z 0) with 0 in Hc5.                                   (* [comment removed for export] *)
  apply leb_spec in Hc4. change (to_Z 4611686018427387904) with (2 ^ 62) in Hc4.
  apply negb_true_iff in Hc3. apply eqb_false_spec in Hc3.        (* [comment removed for export] *)
  apply negb_true_iff in Hc2. apply mem_int_false in Hc2.         (* [comment removed for export] *)
  apply negb_true_iff in Hc1. apply eqb_false_spec in Hc1.        (* [comment removed for export] *)
  pose proof (proj1 (forallb_forall _ _) Hc0) as Hnoent.
  assert (Hlo0 : to_Z (rg_lo rg1) = 0) by (rewrite Hc6; reflexivity).
  pose proof HDI as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  pose proof (Rn_R _ _ _ _ _ _ HRn H0) as HR.
  set (M' := iremove t1 (f_mem F)).
  assert (Hsub : forall t rg, iget t M' = Some rg -> t <> t1 /\ iget t (f_mem F) = Some rg).
  { intros t rg Hg. unfold M' in Hg. rewrite iget_iremove in Hg. destruct (t =? t1)%uint63 eqn:E; [discriminate|].
    apply eqb_false_spec in E. split; [exact E | exact Hg]. }
  assert (Hkeepg : forall t, t <> t1 -> iget t M' = iget t (f_mem F)).
  { intros t Hne. unfold M'. apply iget_iremove_other. intros E. apply Hne. symmetry. exact E. }
  split; [|split; [|split]].
  - (* [comment removed for export] *)
    split.
    { intros rho'' Hag. pose proof (HRn rho'' Hag) as HR''. destruct HR'' as [P1 P2 P3 P4 [Pm Psep]].
      constructor; cbn [drop_region f_pc f_regs f_mem f_resv]; try assumption. fold M'. split.
      - intros t rg Hg. destruct (Hsub t rg Hg) as [_ Hg0]. exact (Pm t rg Hg0).
      - intros ta tb rga rgb Hne Ha Hb. exact (Psep ta tb rga rgb Hne (proj2 (Hsub _ _ Ha)) (proj2 (Hsub _ _ Hb))). }
    split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
    split.
    { intros t rg Hg. cbn [drop_region f_mem] in Hg. fold M' in Hg. exact (Hcov t rg (proj2 (Hsub t rg Hg))). }
    split.
    { destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). cbn [drop_region f_mem]. fold M'. split; [|split].
      - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) Hm1 e He) as Hok.
        assert (Hte : fent_tag e <> t1).
        { pose proof (Hnoent e (in_or_app _ _ _ (or_introl He))) as Hb. apply negb_true_iff in Hb.
          apply eqb_false_spec in Hb. exact Hb. }
        apply (ent_ok_ext rho rho (f_mem F) M' _ _ e eq_refl (Hkeepg _ Hte) (fun q Hq => Hq) Hok).
      - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) Hm2 e He) as Hok.
        assert (Hte : fent_tag e <> t1).
        { pose proof (Hnoent e (in_or_app _ _ _ (or_intror He))) as Hb. apply negb_true_iff in Hb.
          apply eqb_false_spec in Hb. exact Hb. }
        apply (ent_ok_ext rho rho (f_mem F) M' _ _ e eq_refl (Hkeepg _ Hte) (fun q Hq => Hq) Hok).
      - exists rgb. split; [|exact Hbrk]. rewrite Hkeepg; [exact Hgb|]. intros E. apply Hc1. symmetry. exact E. }
    split; [exact I|]. split; [exact HXI|]. split; [exact Hxt|].
    intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem]. cbn [drop_region f_mem]. fold M'.
    assert (Hne : t <> t1) by (intros ->; contradiction).
    split; [exact (pristine_eq _ _ _ (Hkeepg t Hne) Hpr)|].
    intros rg x Hg Hx. rewrite (Hkeepg t Hne) in Hg. exact (Hmem rg x Hg Hx).
  - (* [comment removed for export] *)
    destruct HL as [Hpi Hreg Hpw Hml Hsubc HAb Hlim Hex Hexna Hexlz H9a H9b Htags HE Hacc Hwfna Hwflz].
    constructor; try assumption.
    + intros t rg pn p x Hg Hpn Hp Hx Hlzp. cbn [drop_region f_mem] in Hg. fold M' in Hg.
      exact (Hreg t rg pn p x (proj2 (Hsub t rg Hg)) Hpn Hp Hx Hlzp).
    + eapply Forall_impl; [|exact H9b]. intros e0 [He0|[He0|He0]]; [left; exact He0 | right; left; exact He0 |].
      right; right. cbn [drop_region f_mem]. rewrite iget_iremove.
      destruct (fent_tag e0 =? t1)%uint63; [reflexivity | exact He0].
  - (* [comment removed for export] *)
    destruct HS as [Hz Hspcov Hsp Hexc]. constructor; [| exact Hspcov | | exact Hexc].
    + intros x Hx Hno Hnex.
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (rho t1))) as [Hlow|Hge].
      { apply (Hz x Hx); [|exact Hnex]. intros t rg Hg Hin. destruct (Uint63.eqb t t1) eqn:E.
        - apply Uint63.eqb_spec in E. subst t. rewrite Hg1 in Hg. injection Hg as <-. unfold in_ival in Hin. lia.
        - apply eqb_false_spec in E. apply (Hno t rg); [|exact Hin].
          cbn [drop_region f_mem]. fold M'. rewrite (Hkeepg t E). exact Hg. }
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (rho t1) + to_Z (rg_len rg1))) as [Hin1|Hhigh].
      2:{ apply (Hz x Hx); [|exact Hnex]. intros t rg Hg Hin. destruct (Uint63.eqb t t1) eqn:E.
          - apply Uint63.eqb_spec in E. subst t. rewrite Hg1 in Hg. injection Hg as <-. unfold in_ival in Hin. lia.
          - apply eqb_false_spec in E. apply (Hno t rg); [|exact Hin].
            cbn [drop_region f_mem]. fold M'. rewrite (Hkeepg t E). exact Hg. }
      (* [comment removed for export] *)
      destruct (proj1 (R_mem _ _ _ _ _ HR) t1 rg1 Hg1) as [Hreg1 Hpg1].
      pose proof (region_ok_nowrap rho t1 rg1 Hreg1) as Hnw.
      set (o := bv_unsigned x - bv_unsigned (rho t1)).
      set (pn := of_Z (o / 4096)).
      pose proof (i63_range (rg_len rg1)) as Hlr.
      assert (Hpnz : to_Z pn = o / 4096).
      { unfold pn. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). unfold o.
        clear - Hge Hin1 Hc4 Hlr. Z.div_mod_to_equations. lia. }
      assert (Hpn50 : to_Z pn < 2 ^ 50) by (rewrite Hpnz; unfold o; clear - Hge Hin1 Hc4; Z.div_mod_to_equations; lia).
      assert (Hpage : page_at IM rg1 t1 pn = Some (PG true PKZero iempty)).
      { unfold page_at. destruct (iget pn (rg_pages rg1)) as [p0|] eqn:Ep; [pose proof (Hnop pn p0 Ep); discriminate|].
        rewrite (fxs_eqb_false t1 0%uint63) by (change (to_Z 0) with 0; intros E; apply Hc3; apply to_Z_inj; exact E).
        rewrite Ed1.
        assert (Epr : page_in_region rg1 pn = true).
        { unfold page_in_region. rewrite !andb_true_iff. split; [split; [split|]|].
          - apply ltb_spec. change (to_Z 1125899906842624) with (2 ^ 50). exact Hpn50.
          - apply leb_spec. rewrite (fxs_to_Z_lsl12 pn Hpn50), Hlo0. pose proof (i63_range pn). lia.
          - apply orb_true_iff. right. apply andb_true_iff. split.
            + apply ltb_spec. rewrite (fxs_to_Z_lsl12 pn Hpn50), Hpnz. unfold o. clear - Hge Hin1. Z.div_mod_to_equations. lia.
            + apply Uint63.eqb_spec. apply to_Z_inj.
              rewrite (i63_land_ones (rg_len rg1) 7%uint63 3 eq_refl ltac:(lia)). change (2 ^ 3) with 8. exact Hc5.
          - apply leb_spec. change (to_Z 4611686018427387904) with (2 ^ 62). exact Hc4. }
        rewrite Epr. reflexivity. }
      destruct (Hpg1 pn _ Hpn50 Hpage) as ((Hwr & Hcells & _) & _ & _).
      set (j := o mod 4096).
      assert (Hj : 0 <= j < 4096) by (unfold j; apply Z.mod_pos_bound; lia).
      assert (Hjc : j / 8 < clim rg1 pn /\ j < 8 * clim rg1 pn).
      { unfold clim. rewrite Hpnz. unfold j, o. clear - Hge Hin1 Hc5. Z.div_mod_to_equations. lia. }
      assert (Ex : x = adr rho t1 (to_Z pn * 4096 + j)).
      { apply bv_eq. rewrite fxs_adr_unsigned.
        - rewrite Hpnz. unfold j, o. clear. Z.div_mod_to_equations. lia.
        - rewrite Hpnz. unfold j, o. clear - Hge. Z.div_mod_to_equations. lia.
        - rewrite Hpnz. unfold j, o. pose proof (u64 x). clear - Hge H. Z.div_mod_to_equations. lia. }
      split.
      * set (ci := of_Z (j / 8)). set (k := Z.to_nat (j mod 8)).
        assert (Hci : to_Z ci = j / 8).
        { unfold ci. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). clear - Hj. Z.div_mod_to_equations. lia. }
        assert (Hcell : cell_at IM (PG true PKZero iempty) pn ci = Some fv0).
        { unfold cell_at. cbn [pg_cells pg_kind]. rewrite iget_iempty. reflexivity. }
        assert (Hk : (k < 8)%nat) by (unfold k; clear - Hj; pose proof (Z.mod_pos_bound j 8 ltac:(lia)); lia).
        pose proof (Hcells ci fv0 ltac:(rewrite Hci; clear - Hj Hjc; split; [Z.div_mod_to_equations; lia | exact (proj1 Hjc)]) Hcell k Hk) as Hrv.
        replace (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat k) with (to_Z pn * 4096 + j) in Hrv.
        2:{ rewrite Hci. unfold k. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). clear. Z.div_mod_to_equations. lia. }
        rewrite <- Ex in Hrv. rewrite Hrv.
        unfold fv0. rewrite (fk_dv_conc rho w_zero H0), wbv_w_zero. unfold wbytes8, w0.
        change (bv_unsigned (Z_to_bv 64 0)) with 0. apply fxs_zero_bytes. exact Hk.
      * rewrite Ex. exact (Hwr eq_refl j (conj (proj1 Hj) (proj2 Hjc))).
    + intros t rg Hg. cbn [drop_region f_mem] in Hg. fold M' in Hg. destruct (Hsub t rg Hg) as [Hne Hg0].
      pose proof (Hsp t rg Hg0) as Hok. unfold span_ok in *. cbn [drop_region f_mem]. fold M'.
      destruct (rg_kind rg) as [|q] eqn:Ek; [exact Hok|].
      destruct Hok as (Et & rgq & Hgq & Hrest). split; [exact Et|]. exists rgq. split; [|exact Hrest].
      rewrite Hkeepg; [exact Hgq|]. intros E. subst q.
      unfold no_shadow_child in Hc. rewrite <- Et, Hg0, Ek in Hc. discriminate.
  - (* [comment removed for export] *)
    destruct HX as (X1 & X2 & X3 & X4 & X5). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    split; [|exact X5].
    intros x Hx. destruct (X4 x Hx) as (Ht & Hno & Hm). split; [exact Ht|]. split; [|exact Hm].
    intros t rg Hg Hin. cbn [drop_region f_mem] in Hg. fold M' in Hg. exact (Hno t rg (proj2 (Hsub t rg Hg)) Hin).
Qed.

Theorem sys_unmap3p_sound n rho F L3 ms m t off len res :
  sys_unmap3p Lim keep F L3 n t off len = Some res ->
  D3 n rho F L3 ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 215 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  SOK n rho F L3 res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha0 Ha1. unfold sys_unmap3p in Hsys.
  destruct (shadow_clean keep (fl3 L3) (f_mem F) (t + 1)%uint63) eqn:Hcl.
  - pose proof (DInv3_drop_shadow n rho F L3 ms m _ HD Hcl) as HD0.
    apply (sys_ok3_pre n rho F (drop_region F (t + 1)%uint63) L3 res ms m).
    { apply mfr_drop_region. intros rg pn Hg. unfold shadow_clean in Hcl. rewrite Hg in Hcl.
      destruct (rg_kind rg); [discriminate|]. destruct (rg_dflt rg) as [[| |]|]; try discriminate.
      repeat match type of Hcl with (_ && _ = true) => apply andb_true_iff in Hcl as [Hcl _] end.
      destruct (iget pn (rg_pages rg)) as [p|] eqn:Ep; [|reflexivity].
      pose proof (proj1 (iall_spec _ _) Hcl pn p Ep). discriminate. }
    exact (sys_unmap3_sound cfg segs IM R0 Lim keep mem0 XI xtags XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
             n rho (drop_region F (t + 1)%uint63) L3 ms m t off len res Hsys HD0 Hat Hstep Hx8 Ha0 Ha1).
  - exact (sys_unmap3_sound cfg segs IM R0 Lim keep mem0 XI xtags XI_vm fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0
             n rho F L3 ms m t off len res Hsys HD Hat Hstep Hx8 Ha0 Ha1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rebound_kinds M t rg clo chi :
  iget t M = Some rg -> same_kinds M (iset t (rebound rg clo chi) M).
Proof.
  intros Hg t'. rewrite iget_iset. destruct (t' =? t)%uint63 eqn:E; [|reflexivity].
  apply Uint63.eqb_spec in E. subst t'. rewrite Hg. reflexivity.
Qed.

Lemma DInv3_rebound n rho F L3 ms m t rg clo chi :
  D3 n rho F L3 ms m -> iget t (f_mem F) = Some rg -> to_Z t < to_Z n ->
  to_Z clo <= bv_unsigned (rho t) <= to_Z chi ->
  D3 n rho (set_bounds F t rg clo chi) L3 ms m.
Proof.
  intros (HDI & HL & HS & HX) Hg Ht Hb.
  pose proof (rebound_shape (f_mem F) t rg clo chi Hg) as Hshape.
  pose proof (rebound_kinds (f_mem F) t rg clo chi Hg) as Hkinds.
  split; [exact (DInv_rebound cfg segs IM R0 BIG RTgt keep mem0 XI xtags n rho F (fl3 L3) ms (erase m) t rg clo chi HDI Hg Ht Hb)|].
  split.
  { apply (lazy_part_next IM R0 Lim na0 lz0 A0 n rho F (set_bounds F t rg clo chi) L3 m m);
      [|exact (lazy_frame_refl m) | exact (lp_pi _ _ _ _ _ _ _ _ _ _ _ HL) | exact (lp_mat _ _ _ _ _ _ _ _ _ _ _ HL) | | exact HL].
    2:{ intros t' Hno. unfold set_bounds. cbn [f_mem]. rewrite iget_iset.
        destruct (t' =? t)%uint63 eqn:E; [|exact Hno]. apply Uint63.eqb_spec in E. subst t'. rewrite Hg in Hno. discriminate Hno. }
    pose proof (lazy_part_LZ IM R0 Lim na0 lz0 A0 n rho F L3 m HL) as HLZ.
    intros t' rg' pn p x Hg' Hpn Hp Hx Hlzp. unfold set_bounds in Hg'. cbn [f_mem] in Hg'. rewrite iget_iset in Hg'.
    destruct (t' =? t)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst t'. injection Hg' as <-.
      exact (HLZ t rg pn p x Hg Hpn Hp Hx Hlzp).
    - exact (HLZ t' rg' pn p x Hg' Hpn Hp Hx Hlzp). }
  split.
  - destruct HS as [Hz Hcov Hsp Hexc]. constructor; [| exact Hcov | | exact Hexc].
    + intros x Hx Hno Hnex. apply (Hz x Hx); [|exact Hnex]. exact (no_region_shape' rho _ _ _ Hshape Hno).
    + intros t' rg' Hg'. destruct (same_shape_get _ _ _ _ Hshape Hg') as (rg0 & Hg0 & _).
      exact (span_ok_shape R0 rho _ _ t' rg0 rg' Hshape Hkinds Hg0 Hg' (Hsp t' rg0 Hg0)).
  - destruct HX as (X1 & X2 & X3 & X4 & X5). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    split; [|exact X5].
    intros x Hx. destruct (X4 x Hx) as (Hta & Hno & Hm). split; [exact Hta|]. split; [|exact Hm].
    exact (no_region_shape rho _ _ _ Hshape Hno).
Qed.

(* [comment removed for export] *)
Lemma whole_entry_misses_span n rho F L3 ms m t rg :
  D3 n rho F L3 ms m -> iget t (f_mem F) = Some rg -> to_Z (rg_lo rg) = 0 -> t <> 0%uint63 ->
  In (t, 0%uint63, rg_len rg) (fl_maps (fl3 L3)) ->
  bv_unsigned (rho t) + to_Z (rg_len rg) <= span_lo \/ span_hi <= bv_unsigned (rho t).
Proof.
  intros (HDI & HL & HS & _) Hg Hlo0 Ht0 Hwhole.
  pose proof HDI as (_ & _ & _ & _ & Hli & Hcov & _).
  pose proof (lp_maps _ _ _ _ _ _ _ _ _ _ _ HL) as Hex. pose proof (lp_v2in _ _ _ _ _ _ _ _ _ _ _ HL) as H9a.
  pose proof (sp_cov _ _ _ _ _ _ HS) as Hspcov.
  pose proof (li_disj _ _ _ _ _ Hli) as Hpw.
  change (vm_maps (m_vmmaps (erase m))) with (vm_maps (m_vmmaps m)) in Hpw. rewrite Hex in Hpw.
  set (e0 := (t, 0%uint63, rg_len rg)).
  assert (He0 : In e0 (fl_all L3)) by (exact (proj1 (Forall_forall _ _) H9a e0 Hwhole)).
  pose proof (i63_range (rg_len rg)) as Hlr. pose proof (u64 (rho t)) as Hrt.
  assert (Hden0 : e_lo (den rho e0) = bv_unsigned (rho t) /\ e_hi (den rho e0) = bv_unsigned (rho t) + to_Z (rg_len rg)).
  { unfold e0, e_hi, e_lo, e_sz. cbn [den fst snd]. rewrite to_Z_0, adr_0, u64_lit by lia. split; reflexivity. }
  destruct (Hcov t rg Hg) as [Hne _].
  destruct (Z_le_gt_dec (bv_unsigned (rho t) + to_Z (rg_len rg)) span_lo) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec span_hi (bv_unsigned (rho t))) as [Hh|Hh]; [right; exact Hh|]. exfalso.
  set (x := Z.max (bv_unsigned (rho t)) span_lo).
  assert (Hxs : in_span x) by (unfold in_span, x, span_lo, span_hi in *; lia).
  destruct (Hspcov x Hxs) as (e & He & Et & Hpx).
  assert (Hneq : e <> e0).
  { intros ->. unfold e0 in Et. cbn [fent_tag fst] in Et. exact (Ht0 Et). }
  pose proof (pw_disj_map_In (den rho) _ e e0 Hpw He He0 Hneq) as Hd.
  unfold e_disj in Hd. destruct Hden0 as [D1 D2]. rewrite D1, D2 in Hd. unfold x in Hpx. lia.
Qed.

Lemma DInv3_snap n rho F L3 ms m t :
  D3 n rho F L3 ms m -> D3 n rho (snap (fl3 L3) n F t) L3 ms m.
Proof.
  intros HD. unfold snap. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|exact HD].
  match goal with |- context [if ?c then _ else _] => destruct c eqn:Hchk end; [|exact HD].
  repeat match type of Hchk with (_ && _ = true) =>
    let H := fresh "Hc" in apply andb_true_iff in Hchk as [Hchk H] end.
  apply ltb_spec in Hchk. apply Uint63.eqb_spec in Hc1. apply negb_true_iff in Hc0. apply eqb_false_spec in Hc0.
  apply mem_fent_In in Hc.
  assert (Hlo0 : to_Z (rg_lo rg) = 0) by (rewrite Hc1; reflexivity).
  pose proof (whole_entry_misses_span n rho F L3 ms m t rg HD Hg Hlo0 Hc0 Hc) as Hmiss.
  apply (DInv3_rebound n rho F L3 ms m t rg _ _ HD Hg Hchk).
  pose proof (DInv3_R cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 n rho F L3 ms m HD) as HR.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hg) as (_ & _ & _ & _ & _ & [Hclo Hchi] & _).
  unfold snap_bounds. cbv zeta.
  destruct ((rg_clo rg <? 4611686018427387904)%uint63 && (rg_len rg <=? 4611686018427387904)%uint63) eqn:Eg;
    cbn [fst snd]; [|split; assumption].
  apply andb_true_iff in Eg as [G1 G2]. apply ltb_spec in G1. apply leb_spec in G2.
  change (to_Z 4611686018427387904) with (2 ^ 62) in G1, G2.
  pose proof (i63_range (rg_clo rg)) as Hc0r. pose proof (i63_range (rg_len rg)) as Hlr.
  assert (Hadd : to_Z (rg_clo rg + rg_len rg)%uint63 = to_Z (rg_clo rg) + to_Z (rg_len rg)).
  { rewrite add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  split.
  - destruct ((span_lo_i <? rg_clo rg + rg_len rg)%uint63 && (rg_clo rg <? span_hi_i)%uint63) eqn:E1; [|exact Hclo].
    apply andb_true_iff in E1 as [E1 _]. apply ltb_spec in E1. rewrite Hadd in E1.
    change (to_Z span_lo_i) with span_lo in E1. change (to_Z span_hi_i) with span_hi.
    destruct Hmiss as [Hl|Hh]; lia.
  - destruct ((rg_chi rg <? span_hi_i)%uint63 && (rg_len rg <=? span_lo_i)%uint63
              && (span_lo_i - rg_len rg <? rg_chi rg)%uint63) eqn:E2; [|exact Hchi].
    apply andb_true_iff in E2 as [E2 _]. apply andb_true_iff in E2 as [E2 E3].
    apply ltb_spec in E2. apply leb_spec in E3.
    change (to_Z span_hi_i) with span_hi in E2. change (to_Z span_lo_i) with span_lo in E3.
    assert (Hsub : to_Z (span_lo_i - rg_len rg)%uint63 = span_lo - to_Z (rg_len rg)).
    { rewrite sub_spec. change (to_Z span_lo_i) with span_lo. apply Z.mod_small. change wB with (2 ^ 63).
      unfold span_lo in *. lia. }
    rewrite Hsub. destruct Hmiss as [Hl|Hh]; lia.
Qed.

(* [comment removed for export] *)
Lemma DInv3_refine3 n rho F L3 ms m t thr Fa Fb :
  D3 n rho F L3 ms m -> refine3 (fl3 L3) F n t thr = Some (Fa, Fb) ->
  D3 n rho Fa L3 ms m \/ D3 n rho Fb L3 ms m.
Proof.
  intros HD Href. unfold refine3 in Href.
  destruct (refine_region F n t thr) as [[Fa0 Fb0]|] eqn:Hr; [|discriminate]. injection Href as <- <-.
  cut (D3 n rho Fa0 L3 ms m \/ D3 n rho Fb0 L3 ms m).
  { intros [H|H]; [left | right]; apply DInv3_snap; exact H. }
  unfold refine_region in Hr.
  destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  match type of Hr with (if ?c then _ else _) = _ => destruct c eqn:C end; [|discriminate].
  injection Hr as <- <-.
  repeat match type of C with (_ && _ = true) =>
    let H' := fresh "Hc" in apply andb_true_iff in C as [C H'] end.
  apply ltb_spec in C, Hc0. apply leb_spec in Hc3, Hc1, Hc. apply Uint63.eqb_spec in Hc2.
  apply (f_equal to_Z) in Hc2. rewrite to_Z_land4095 in Hc2. change (to_Z 0) with 0 in Hc2.
  change (to_Z 12) with 12 in Hc3. change (to_Z 4096) with 4096 in Hc1.
  pose proof (DInv3_R cfg segs IM R0 Lim keep mem0 XI xtags fr0 fc0 rom0 hi wb0 na0 lz0 brk0 A0 n rho F L3 ms m HD) as HR.
  pose proof (R_region_ok _ _ _ _ _ _ _ HR Hg) as (_ & _ & _ & _ & Hal & [Hclo Hchi] & _).
  pose proof (align_4096 R0 _ _ Hc3 Hal) as Hal12.
  assert (Hsub : to_Z (thr - 4096)%uint63 = to_Z thr - 4096).
  { rewrite sub_spec. change (to_Z 4096) with 4096. pose proof (i63_range thr) as Hthr. apply Z.mod_small.
    change wB with (2 ^ 63). clear - Hthr Hc1. lia. }
  destruct (Z_lt_le_dec (bv_unsigned (rho t)) (to_Z thr)) as [Hlt|Hge].
  - left. apply (DInv3_rebound n rho F L3 ms m t rg _ _ HD Hg C). rewrite Hsub. split; [exact Hclo|].
    assert (E1 : bv_unsigned (rho t) = 4096 * (bv_unsigned (rho t) / 4096)) by (apply Z.div_exact; [clear; lia | exact Hal12]).
    assert (E2 : to_Z thr = 4096 * (to_Z thr / 4096)) by (apply Z.div_exact; [clear; lia | exact Hc2]).
    clear - Hlt E1 E2. lia.
  - right. apply (DInv3_rebound n rho F L3 ms m t rg _ _ HD Hg C). split; [exact Hge | exact Hchi].
Qed.

End Drive3S.
