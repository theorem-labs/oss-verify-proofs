(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff FxLazy FxCellFrame
  FxDrive FxDrive3.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound BackingAlgebra.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound CxOpt.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrLedger BrMain BrRev BrRevLedger BrClass BrRevS BrDress BrGrow BrTrans BrRa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ents3.
Variable E : AX2.env.
Variable TT : ttab_e.
Local Notation rho := (rho_of TT E).

Definition ent_chk3 (m : CAP.amap) (e : fent) : bool :=
  let '(t, off, len) := e in
  match CAP.am_len m with
  | AX2.ELit l => (l =? to_Z len) && lin_match (AX2.lin_of (CAP.am_base m)) (AX2.lin_of (tte TT t)) (to_Z off)
  | _ => false
  end.

Lemma ent_chk3_den m e : ent_chk3 m e = true -> CXS.amap_den E m = den rho e.
Proof.
  destruct e as [[t off] len]. unfold ent_chk3.
  destruct (CAP.am_len m) as [l| | | | | | |] eqn:El; try discriminate.
  intros Hc. apply andb_prop in Hc as [Hl Hm]. apply Z.eqb_eq in Hl. subst l.
  pose proof (lin_match_sound E _ _ _ Hm) as Hq.
  pose proof (AX2S.lin_of_sound E (CAP.am_base m)) as Hb.
  assert (Ht : AX2S.eqm (AX2S.lden E (AX2.lin_of (tte TT t))) (bv_unsigned (rho t))) by (rewrite (rho_tte E TT t); apply AX2S.lin_of_sound).
  unfold CXS.amap_den, den. rewrite El. cbn [AX2.edenot]. f_equal.
  apply bv_eq. unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r.
  pose proof (br_u64 (AX2.edenot E (CAP.am_base m))) as Hu.
  destruct Hq as [q1 Hq1]. destruct Hb as [q2 Hb2]. destruct Ht as [q3 Ht3]. unfold AX2S.uE in *.
  apply (Z.mod_unique_pos _ _ (q2 - q3 - q1)); [exact Hu|]. lia.
Qed.

Fixpoint ents_chk3 (ms : list CAP.amap) (es : list fent) : bool :=
  match ms, es with
  | [], [] => true
  | m :: ms', e :: es' => ent_chk3 m e && ents_chk3 ms' es'
  | _, _ => false
  end.

Lemma ents3_den : forall ms es, ents_chk3 ms es = true -> map (CXS.amap_den E) ms = map (den rho) es.
Proof.
  induction ms as [|m ms IH]; intros [|e es] Hc; cbn [ents_chk3] in Hc; try discriminate; [reflexivity|].
  apply andb_prop in Hc as [H1 H2]. cbn [map]. rewrite (ent_chk3_den m e H1), (IH es H2). reflexivity.
Qed.

Lemma ents3_nth : forall ms es i m e, ents_chk3 ms es = true -> nth_error ms i = Some m -> nth_error es i = Some e ->
  ent_chk3 m e = true.
Proof.
  induction ms as [|m0 ms IH]; intros [|e0 es] i m e Hc Hm He; cbn [ents_chk3] in Hc; try discriminate; [destruct i; discriminate|].
  apply andb_prop in Hc as [H1 H2]. destruct i as [|i]; cbn [nth_error] in Hm, He.
  - injection Hm as <-. injection He as <-. exact H1.
  - exact (IH es i m e H2 Hm He).
Qed.
End Ents3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint coverZ (l : list (Z * Z)) (fuel : nat) (pos hi : Z) : bool :=
  if hi <=? pos then true else
  match fuel with
  | O => false
  | Datatypes.S f => match List.find (fun p => (fst p <=? pos) && (pos <? snd p)) l with
           | Some p => coverZ l f (snd p) hi
           | None => false
           end
  end.

Lemma coverZ_sound : forall l fuel pos hi, coverZ l fuel pos hi = true ->
  forall z, pos <= z < hi -> exists p, In p l /\ fst p <= z < snd p.
Proof.
  intros l. induction fuel as [|f IH]; intros pos hi Hc z Hz; cbn [coverZ] in Hc;
    (destruct (hi <=? pos) eqn:Eh; [apply Z.leb_le in Eh; lia|]); [discriminate|].
  destruct (List.find (fun p => (fst p <=? pos) && (pos <? snd p)) l) as [p|] eqn:Ef; [|discriminate].
  destruct (List.find_some _ _ Ef) as [Hin Hp]. apply andb_prop in Hp as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Z_lt_dec z (snd p)) as [Hlt|Hge].
  - exists p. split; [exact Hin | lia].
  - apply (IH (snd p) hi Hc z). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Root.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis HULL_ok : CXS.hull_ok A.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Variable TT : ttab_e.
Hypothesis HTT : tt_wf TT = true.

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).
Local Notation R0 := (segments_reserved segs).
Local Notation kn := (CAP.kn CS).

(* [comment removed for export] *)
Definition res_chk : bool :=
  (CAP.img_lo A <? CAP.img_hi A) &&
  forallb (fun p => (CAP.img_lo A <=? e_lo p) && (e_hi p <=? CAP.img_hi A) && (e_lo p mod 8 =? 0) && (e_hi p mod 8 =? 0)) R0
  && coverZ (map (fun p => (e_lo p, e_hi p)) R0) (Datatypes.S (length R0)) (CAP.img_lo A) (CAP.img_hi A).

Lemma res_in_hull : res_chk = true ->
  Forall (fun p => CAP.img_lo A <= e_lo p /\ e_hi p <= CAP.img_hi A) R0.
Proof.
  unfold res_chk. intros Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hc.
  apply Forall_forall. intros p Hp. specialize (Hc p Hp).
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1, H2. tauto.
Qed.

Lemma res_al8 : res_chk = true -> Forall (fun p => e_lo p mod 8 = 0 /\ e_hi p mod 8 = 0) R0.
Proof.
  unfold res_chk. intros Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hc.
  apply Forall_forall. intros p Hp. specialize (Hc p Hp).
  apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [_ H3]. apply Z.eqb_eq in H3, H4. tauto.
Qed.

Lemma res_cover_ex : res_chk = true -> forall z, CAP.img_lo A <= z < CAP.img_hi A ->
  exists p, In p R0 /\ e_lo p <= z < e_hi p.
Proof.
  unfold res_chk. intros Hc z Hz. apply andb_prop in Hc as [_ Hc].
  destruct (coverZ_sound _ _ _ _ Hc z Hz) as (q & Hq & Hzq).
  apply in_map_iff in Hq as (p & <- & Hp). exists p. split; [exact Hp | exact Hzq].
Qed.

Lemma res_hull_ne : res_chk = true -> CAP.img_lo A < CAP.img_hi A.
Proof.
  unfold res_chk. intros Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.ltb_lt in Hc. exact Hc.
Qed.

Lemma res_cover : res_chk = true -> forall z, CAP.img_lo A <= z < CAP.img_hi A -> CXS.in_ivs z R0 = true.
Proof.
  intros Hc z Hz. destruct (res_cover_ex Hc z Hz) as (p & Hp & Hzp).
  unfold CXS.in_ivs. apply existsb_exists. exists p. split; [exact Hp|].
  unfold e_hi, e_lo, e_sz in Hzp. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Definition lo_pos_chk : bool :=
  forallb (fun am => match AX2.base_range kn (CAP.am_base am) with Some (lo, _) => 0 <? lo | None => false end) (CAP.a_maps CS).

Lemma lo_pos : lo_pos_chk = true -> Forall (fun p => 0 < e_lo p) (vm_maps V).
Proof.
  intros Hc. rewrite (CxOpt.maps_exact_D1 E _ _ Hlx (CXS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)).
  apply Forall_forall. intros p Hp. apply in_map_iff in Hp as (am & <- & Ham).
  unfold lo_pos_chk in Hc. rewrite forallb_forall in Hc. specialize (Hc am Ham).
  destruct (AX2.base_range kn (CAP.am_base am)) as [[lo hi]|] eqn:Hr; [|discriminate]. apply Z.ltb_lt in Hc.
  destruct (AX2S.base_range_sound segs E _ kn _ lo hi (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hr) as [Hlo _].
  unfold e_lo, CXS.amap_den. cbn [fst]. lia.
Qed.

(* [comment removed for export] *)
Variable W : Z.          (* [comment removed for export] *)
Variables c S : Z.

Definition led_chk : bool :=
  res_chk && lo_pos_chk
  && (Z.of_nat (length (CAP.a_maps CS)) <=? c)
  && (CAP.a_totsz CS - live_bytes R0 <=? S)
  && (0 <? W) && (W <? 2 ^ 64) && (W mod 4096 =? 0) && (reserved_top R0 <=? W).

Theorem rb3_ledger_inv : led_chk = true -> ledger_inv R0 BIG c S (erase_vm (Z_to_bv 64 W) V).
Proof.
  unfold led_chk. intros Hc.
  apply andb_prop in Hc as [Hc HW4]. apply andb_prop in Hc as [Hc HW3]. apply andb_prop in Hc as [Hc HW2].
  apply andb_prop in Hc as [Hc HW1]. apply andb_prop in Hc as [Hc HS]. apply andb_prop in Hc as [Hc Hcnt].
  apply andb_prop in Hc as [Hres Hpos].
  apply Z.leb_le in HW4, HS, Hcnt. apply Z.ltb_lt in HW1, HW2. apply Z.eqb_eq in HW3.
  destruct (cs_maps_facts segs A Lim SINV argH ISP FS0 E CS R FULL m HCS (res_in_hull Hres))
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (lo_pos Hpos) as Hlp.
  assert (EW : bv_unsigned (Z_to_bv 64 W) = W) by (apply br_lit_small; lia).
  constructor; cbn [erase_vm vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_init_sp].
  - exact F1.
  - apply Z.le_refl.   (* [comment removed for export] *)
  - exact (proj1 F8).
  - exact (proj2 F8).
  - exact F3.
  - exact F4.
  - apply Forall_forall. intros p Hp. split; [exact (proj1 (Forall_forall _ _) Hlp p Hp)|].
    exact (proj1 (Forall_forall _ _) F5 p Hp).
  - exact F6.
  - exact F7.
  - rewrite (CxOpt.maps_exact_D1 E _ _ Hlx (CXS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)), length_map. exact Hcnt.
  - pose proof (CXS.co_totsz _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Ht. rewrite sum_sizes_live, live_bytes_app, F1 in Ht. lia.
  - constructor.
  - rewrite EW. exact HW1.
  - rewrite EW. exact HW3.
  - lia.
  - rewrite EW. exact HW4.
Qed.

End Root.

(* [comment removed for export] *)
Lemma led_lx segs A Lim SINV argH ISP FS0 E CS R FULL m W c S :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m -> CAP.no_fog (CAP.a_maps CS) = true ->
  led_chk segs A CS W c S = true -> CxOpt.ledger_exact E (CAP.a_maps CS).
Proof.
  intros HCS Hnf Hled. unfold led_chk in Hled. do 6 (apply andb_prop in Hled as [Hled _]). apply andb_prop in Hled as [_ Hc].
  split; [exact Hnf|]. apply Forall_forall. intros am Ham. right.
  unfold lo_pos_chk in Hc. rewrite forallb_forall in Hc. specialize (Hc am Ham).
  destruct (AX2.base_range (CAP.kn CS) (CAP.am_base am)) as [[lo hi]|] eqn:Hr; [|discriminate]. apply Z.ltb_lt in Hc.
  destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ lo hi (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hr) as [Hlo _].
  unfold CXS.uE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Regions.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis HULL_ok : CXS.hull_ok A.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Variable TT : ttab_e.
Variable classes : list (int * rclass).
Variable M : itrie region.          (* [comment removed for export] *)

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).
Local Notation R0 := (segments_reserved segs).
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis Hres : res_chk segs A = true.

Lemma covered_erase wb x : FxDrive.covered V x -> FxDrive.covered (erase_vm wb V) x.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Definition abs_chk (t : int) (rg : region) : bool :=
  match AX2.base_range (CAP.kn CS) (tte TT t) with
  | Some (blo, bhi) => (blo =? 0) && (bhi =? 0)
  | None => false
  end
  && (CAP.img_lo A <=? 8 * (to_Z (rg_lo rg) - to_Z shadow_K)) && (8 * (to_Z (rg_len rg) - to_Z shadow_K) <=? CAP.img_hi A).

Definition kind_chk (t : int) (rg : region) (c : rclass) : bool :=
  match rg_kind rg with
  | RK_plain => match c with RCSpan => abs_chk t rg | _ => true end
  | RK_shadow p =>
      (t =? p + 1)%uint63
      && match iget p M with
         | Some rgp => (3 <=? to_Z (rg_align rgp)) && (to_Z (rg_lo rgp) <=? 8 * to_Z (rg_lo rg))
                       && (8 * to_Z (rg_len rg) <=? to_Z (rg_len rgp))
         | None => false
         end
  end.

Definition reg3_chk (p : int * region) : bool :=
  let '(t, rg) := p in
  match cls classes t with
  | Some c => class_chk A CS TT t (rg_lo rg) (rg_len rg) c && (to_Z (rg_lo rg) <? to_Z (rg_len rg)) && kind_chk t rg c
  | None => false
  end.

(* [comment removed for export] *)
Definition span_ok_chk : bool := span_chk CS && (CAP.img_hi A <=? span_lo).

Definition regs3_chk : bool := span_ok_chk && forallb reg3_chk (ielements M).

Lemma reg3_get t rg : regs3_chk = true -> iget t M = Some rg ->
  exists c, cls classes t = Some c /\ class_chk A CS TT t (rg_lo rg) (rg_len rg) c = true
            /\ to_Z (rg_lo rg) < to_Z (rg_len rg) /\ kind_chk t rg c = true.
Proof.
  unfold regs3_chk. intros Hc Hg. apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hc.
  pose proof (Hc (t, rg) (proj2 (ielements_spec M t rg) Hg)) as H1. unfold reg3_chk in H1.
  destruct (cls classes t) as [c|]; [|discriminate]. exists c. split; [reflexivity|].
  apply andb_prop in H1 as [H1 H3]. apply andb_prop in H1 as [H1 H2]. apply Z.ltb_lt in H2. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition region_nowr (t : int) (rg : region) : bool :=
  negb (t =? 0)%uint63
  && match rg_dflt rg with
     | None => forallb (fun kv : int * page => negb (pg_wr (snd kv))) (ielements (rg_pages rg))
     | Some _ => false
     end.

Definition span_nclb (a : AX2.saddr) (n : AX2.expr) : bool :=
  (* [comment removed for export] *)
  if CAP.xinsideJ (CAP.kn CS) (AX2.a_base a) (AX2.a_off a) n (AX2.ELit 0) span_lo (AX2.ELit (span_hi - span_lo)) then
  forallb (fun p : int * region =>
       match cls classes (fst p) with
       | Some RCSpan =>
           if region_nowr (fst p) (snd p) then true else
           if match len_hi (CAP.kn CS) n with
              | Some h => (0 <=? to_Z (rg_lo (snd p))) && (to_Z (rg_lo (snd p)) <=? to_Z (rg_len (snd p)))
                          && AX2.ranges_apart (CAP.kn CS) (AX2.a_base a) (AX2.a_off a) h (tte TT (fst p)) (to_Z (rg_lo (snd p)))
                                              (to_Z (rg_len (snd p)) - to_Z (rg_lo (snd p)))
              | None => false
              end then true else
           match AX2.base_range (CAP.kn CS) (AX2.a_base a), AX2.base_range (CAP.kn CS) (tte TT (fst p)), len_hi (CAP.kn CS) n with
           | Some (blo, bhi), Some (rlo, rhi), Some h =>
               (bhi + AX2.a_off a + h <=? rlo + to_Z (rg_lo (snd p))) || (rhi + to_Z (rg_len (snd p)) <=? blo + AX2.a_off a)
           | _, _, _ => false
           end
       | Some _ => true
       | None => false
       end) (ielements M)
  else false.

(* [comment removed for export] *)
Definition span_nclbR (ra : ra_t) (a : AX2.saddr) (n : AX2.expr) : bool :=
  if CAP.xinsideJ (CAP.kn CS) (AX2.a_base a) (AX2.a_off a) n (AX2.ELit 0) span_lo (AX2.ELit (span_hi - span_lo)) then
  forallb (fun p : int * region =>
       match cls classes (fst p) with
       | Some RCSpan =>
           if region_nowr (fst p) (snd p) then true else
           if match len_hi (CAP.kn CS) n with
              | Some h => (0 <=? to_Z (rg_lo (snd p))) && (to_Z (rg_lo (snd p)) <=? to_Z (rg_len (snd p)))
                          && ra (AX2.a_base a) (AX2.a_off a) h (tte TT (fst p)) (to_Z (rg_lo (snd p)))
                                              (to_Z (rg_len (snd p)) - to_Z (rg_lo (snd p)))
              | None => false
              end then true else
           match AX2.base_range (CAP.kn CS) (AX2.a_base a), AX2.base_range (CAP.kn CS) (tte TT (fst p)), len_hi (CAP.kn CS) n with
           | Some (blo, bhi), Some (rlo, rhi), Some h =>
               (bhi + AX2.a_off a + h <=? rlo + to_Z (rg_lo (snd p))) || (rhi + to_Z (rg_len (snd p)) <=? blo + AX2.a_off a)
           | _, _, _ => false
           end
       | Some _ => true
       | None => false
       end) (ielements M)
  else false.

Lemma span_nclbR_eq ra a n : ra = AX2.ranges_apart (CAP.kn CS) -> span_nclbR ra a n = span_nclb a n.
Proof. intros ->. reflexivity. Qed.

Lemma span_nclb_sound (IM : fimage) (mem : word -> option byte) a n :
  regs3_chk = true -> mem_ok segs IM rho M mem ->
  span_nclb a n = true ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + AX2S.elenZ E n -> ~ claimed_wr IM rho M (Z_to_bv 64 x).
Proof.
  intros Hregs Hmem Hc x Hx (t' & rg' & pn & p & j & Hg' & Hpn & Hp & Hwr & Hj & Hhi' & Ex).
  unfold span_nclb in Hc. apply andb_prop in Hc as [Hin Hall].
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
  destruct (CXS.xinsideJ_sound segs E _ (CAP.kn CS) _ _ _ _ _ _ Hkn Hin) as [X1 X2].
  unfold AX2S.estart in X1, X2. cbn [AX2.a_base AX2.a_off AX2.edenot] in X1, X2.
  unfold AX2S.elenZ in X2 at 2. cbn [AX2.edenot] in X2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in X1, X2.
  rewrite (br_lit_small (span_hi - span_lo)) in X2 by (unfold span_lo, span_hi; lia).
  assert (Hxs : span_lo <= x < span_hi) by (unfold AX2S.estart in Hx; lia).
  destruct (proj1 Hmem t' rg' Hg') as [Hrok' Hpages']. destruct (Hpages' pn p Hpn Hp) as (_ & Hlo' & _ & _).
  destruct Hrok' as (_ & _ & Hb63' & _).
  pose proof (br_u64 (rho t')) as Hu'. pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rg_lo rg')) as Hl0'.
  assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply br_lit_small; unfold span_lo, span_hi in Hxs; lia).
  assert (Ux' : bv_unsigned (adr rho t' (to_Z pn * 4096 + j)) = bv_unsigned (rho t') + (to_Z pn * 4096 + j))
    by (apply adr_unsigned; lia).
  assert (Exz : x = bv_unsigned (rho t') + (to_Z pn * 4096 + j)) by (rewrite <- Ux, Ex; exact Ux').
  destruct (reg3_get t' rg' Hregs Hg') as (c & Hcls & Hcl & Hne & _).
  rewrite forallb_forall in Hall. pose proof (Hall (t', rg') (proj2 (ielements_spec M t' rg') Hg')) as H1. cbn [fst snd] in H1.
  rewrite Hcls in H1.
  assert (Hsem : class_sem A CS m c x).
  { apply (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT t' _ _ c Hcl Hb63'). lia. }
  unfold regs3_chk in Hregs. apply andb_prop in Hregs as [Hsok _]. unfold span_ok_chk in Hsok.
  apply andb_prop in Hsok as [Hsc Hih]. apply Z.leb_le in Hih.
  destruct c as [| |i|].
  - apply (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx HULL_ok RCHull RCSpan x); [reflexivity | exact Hsem|].
    cbn [class_sem]. split; [exact Hxs|]. split; [exact Hsc | exact Hih].
  - apply (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx HULL_ok RCTop RCSpan x); [reflexivity | exact Hsem|].
    cbn [class_sem]. split; [exact Hxs|]. split; [exact Hsc | exact Hih].
  - apply (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx HULL_ok (RCEnt i) RCSpan x); [reflexivity | exact Hsem|].
    cbn [class_sem]. split; [exact Hxs|]. split; [exact Hsc | exact Hih].
  - destruct (region_nowr t' rg') eqn:Enw.
    { (* [comment removed for export] *)
      unfold region_nowr in Enw. apply andb_prop in Enw as [Ht0 Enw]. apply negb_true_iff in Ht0.
      destruct (rg_dflt rg') as [kd|] eqn:Ed; [discriminate|]. rewrite forallb_forall in Enw.
      unfold page_at in Hp. destruct (iget pn (rg_pages rg')) as [p1|] eqn:Hpg.
      - injection Hp as <-. pose proof (Enw (pn, p1) (proj2 (ielements_spec _ pn p1) Hpg)) as Hn. cbn [snd] in Hn.
        rewrite Hwr in Hn. discriminate.
      - rewrite Ht0, Ed in Hp. discriminate. }
    destruct (match len_hi (CAP.kn CS) n with
              | Some h => (0 <=? to_Z (rg_lo rg')) && (to_Z (rg_lo rg') <=? to_Z (rg_len rg'))
                          && AX2.ranges_apart (CAP.kn CS) (AX2.a_base a) (AX2.a_off a) h (tte TT t') (to_Z (rg_lo rg'))
                                              (to_Z (rg_len rg') - to_Z (rg_lo rg'))
              | None => false
              end) eqn:Eap.
    { (* [comment removed for export] *)
      destruct (len_hi (CAP.kn CS) n) as [h|] eqn:Hl; [|discriminate].
      apply andb_prop in Eap as [Eap Hra]. apply andb_prop in Eap as [G1 G2]. apply Z.leb_le in G1, G2.
      pose proof (len_hi_sound segs E (CAP.kn CS) _ _ Hkn n h Hl) as Hlh.
      pose proof (AX2S.ranges_apart_sound segs E _ (CAP.kn CS) _ _ _ _ _ _ Hkn Hra) as D1.
      unfold AX2S.estart in D1, Hx. cbn [AX2.a_base AX2.a_off] in D1. rewrite <- (rho_tte E TT t') in D1. lia. }
    destruct (AX2.base_range (CAP.kn CS) (AX2.a_base a)) as [[blo bhi]|] eqn:Hr; [|discriminate].
    destruct (AX2.base_range (CAP.kn CS) (tte TT t')) as [[rlo rhi]|] eqn:Hrr; [|discriminate].
    destruct (len_hi (CAP.kn CS) n) as [h|] eqn:Hl; [|discriminate].
    destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ blo bhi Hkn Hr) as [Hb1 Hb2].
    destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ rlo rhi Hkn Hrr) as [Hr1 Hr2].
    rewrite <- (rho_tte E TT t') in Hr1, Hr2.
    pose proof (len_hi_sound segs E (CAP.kn CS) _ _ Hkn n h Hl) as Hlh.
    unfold AX2S.estart in Hx.
    apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma span_nclb_span a n : span_nclb a n = true ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + AX2S.elenZ E n -> span_lo <= x < span_hi.
Proof.
  intros Hc x Hx. unfold span_nclb in Hc. apply andb_prop in Hc as [Hin _].
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
  destruct (CXS.xinsideJ_sound segs E _ (CAP.kn CS) _ _ _ _ _ _ Hkn Hin) as [X1 X2].
  unfold AX2S.estart in X1, X2. cbn [AX2.a_base AX2.a_off AX2.edenot] in X1, X2.
  unfold AX2S.elenZ in X2 at 2. cbn [AX2.edenot] in X2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in X1, X2.
  rewrite (br_lit_small (span_hi - span_lo)) in X2 by (unfold span_lo, span_hi; lia).
  unfold AX2S.estart in Hx. lia.
Qed.

Lemma span_region_apart t rg c x : regs3_chk = true -> iget t M = Some rg -> cls classes t = Some c -> class_neq c RCSpan = true ->
  bv_unsigned (rho t) + to_Z (rg_lo rg) <= x < bv_unsigned (rho t) + to_Z (rg_len rg) -> span_lo <= x < span_hi -> False.
Proof.
  intros Hregs Hg Hcls Hneq Hx Hxs.
  destruct (reg3_get t rg Hregs Hg) as (c' & Hcls' & Hcl & _ & _). rewrite Hcls in Hcls'. injection Hcls' as <-.
  destruct (HM t rg Hg) as (_ & _ & Hb63 & _).
  pose proof (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT t _ _ c Hcl Hb63 x Hx) as Hsem.
  unfold regs3_chk in Hregs. apply andb_prop in Hregs as [Hsok _]. unfold span_ok_chk in Hsok.
  apply andb_prop in Hsok as [Hsc Hih]. apply Z.leb_le in Hih.
  apply (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx HULL_ok c RCSpan x Hneq Hsem).
  cbn [class_sem]. split; [exact Hxs|]. split; [exact Hsc | exact Hih].
Qed.



Theorem rb3_regions_covered wb : regs3_chk = true -> regions_covered rho M (erase_vm wb V).
Proof.
  intros Hc t rg Hg. destruct (reg3_get t rg Hc Hg) as (c & _ & Hcl & Hlt & _). split; [exact Hlt|].
  intros x Hx. apply covered_erase.
  destruct (HM t rg Hg) as (_ & _ & Hnw & _).
  apply (class_covered segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx (res_cover segs A Hres) c x).
  exact (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT t _ _ c Hcl Hnw x Hx).
Qed.

Theorem rb3_span_ok : regs3_chk = true -> forall t rg, iget t M = Some rg -> span_ok R0 rho M t rg.
Proof.
  intros Hc t rg Hg. destruct (reg3_get t rg Hc Hg) as (c & _ & Hcl & Hlt & Hk).
  unfold regs3_chk, span_ok_chk in Hc. apply andb_prop in Hc as [Hsp _]. apply andb_prop in Hsp as [Hsc Hih]. apply Z.leb_le in Hih.
  destruct (HM t rg Hg) as (_ & _ & Hnw & _).
  pose proof (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT t _ _ c Hcl Hnw) as Hsem.
  unfold span_ok, kind_chk in *. destruct (rg_kind rg) as [|p].
  - destruct (match c with RCSpan => true | _ => false end) eqn:Ec.
    + (* [comment removed for export] *)
      destruct c; try discriminate. right. unfold abs_chk in Hk.
      apply andb_prop in Hk as [Hk H3]. apply andb_prop in Hk as [Hk H2]. apply Z.leb_le in H2, H3.
      destruct (AX2.base_range (CAP.kn CS) (tte TT t)) as [[blo bhi]|] eqn:Hr; [|discriminate].
      apply andb_prop in Hk as [Hb1 Hb2]. apply Z.eqb_eq in Hb1, Hb2. subst blo bhi.
      destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ 0 0 (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hr) as [Hb1 Hb2].
      rewrite <- (rho_tte E TT t) in Hb1, Hb2.
      assert (Er : bv_unsigned (rho t) = 0) by lia. rewrite Er in *.
      destruct (Hsem (0 + to_Z (rg_lo rg)) ltac:(lia)) as (Hs1 & _).
      destruct (Hsem (0 + to_Z (rg_len rg) - 1) ltac:(lia)) as (Hs2 & _).
      split; [lia|]. split; [lia|]. intros y Hy.
      destruct (res_cover_ex segs A Hres (8 * (y - to_Z shadow_K)) ltac:(lia)) as (q & Hq & Hyq).
      exists q. split; [exact Hq|]. split; [lia|].
      pose proof (proj1 (Forall_forall _ _) (res_al8 segs A Hres) q Hq) as [_ Hal].
      clear - Hyq Hal. Z.div_mod_to_equations. lia.
    + (* [comment removed for export] *)
      left.
      destruct (Z_le_dec (bv_unsigned (rho t) + to_Z (rg_len rg)) span_lo) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_dec span_hi (bv_unsigned (rho t) + to_Z (rg_lo rg))) as [H2|H2]; [right; exact H2|].
      exfalso. set (x := Z.max (bv_unsigned (rho t) + to_Z (rg_lo rg)) span_lo).
      assert (Hx1 : bv_unsigned (rho t) + to_Z (rg_lo rg) <= x < bv_unsigned (rho t) + to_Z (rg_len rg)) by (unfold x; lia).
      assert (Hx2 : span_lo <= x < span_hi) by (unfold x, span_lo, span_hi in *; lia).
      apply (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx HULL_ok c RCSpan x).
      * destruct c; try reflexivity. discriminate.
      * exact (Hsem x Hx1).
      * cbn [class_sem]. split; [exact Hx2|]. split; [exact Hsc | exact Hih].
  - apply andb_prop in Hk as [Ht Hp]. apply Uint63.eqb_spec in Ht. split; [exact Ht|].
    destruct (iget p M) as [rgp|] eqn:Hgp; [|discriminate].
    apply andb_prop in Hp as [Hp H3]. apply andb_prop in Hp as [H1 H2]. apply Z.leb_le in H1, H2, H3.
    exists rgp. split; [reflexivity|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

End Regions.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fent_eqb (e e' : fent) : bool :=
  let '(t, o, l) := e in let '(t', o', l') := e' in ((t =? t') && (o =? o') && (l =? l'))%uint63.
Lemma fent_eqb_eq e e' : fent_eqb e e' = true -> e = e'.
Proof.
  destruct e as [[t o] l], e' as [[t' o'] l']. unfold fent_eqb. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_spec in H1, H2, H3. subst. reflexivity.
Qed.
Definition fent_mem (e : fent) (l : list fent) : bool := existsb (fent_eqb e) l.
Lemma fent_mem_In e l : fent_mem e l = true -> In e l.
Proof. unfold fent_mem. intros H. apply existsb_exists in H as (e' & Hin & He). rewrite (fent_eqb_eq _ _ He). exact Hin. Qed.

Lemma page_base_aligned_id (p : word) : bv_unsigned p mod 4096 = 0 -> page_base p = p.
Proof.
  intros Hal. unfold page_base, page_base_of, page_size. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (br_u64 p) as Hu.
  assert (Ep : bv_unsigned p / 4096 * 4096 = bv_unsigned p) by (clear - Hal; Z.div_mod_to_equations; lia).
  rewrite Ep. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). exact Hu.
Qed.

Lemma adr0_lit rho z : rho 0%uint63 = Z_to_bv 64 0 -> adr rho 0 z = Z_to_bv 64 z.
Proof.
  intros H0. unfold adr. rewrite H0. apply bv_eq. rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_mod. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Root2.
Variable segs : list Segment.
Variable IM : fimage.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Variable TT : ttab_e.
Variable classes : list (int * rclass).
Variable M : itrie region.          (* [comment removed for export] *)
Variable n : int.
Variable L3 : fledger3.

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).
Local Notation R0 := (segments_reserved segs).
Local Notation ALL := (fl_all L3).
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis Hres : res_chk segs A = true.
Hypothesis Hregs : regs3_chk A CS TT classes M = true.

(* [comment removed for export] *)
Definition maps3_chk : bool := ents_chk3 TT (CAP.a_maps CS) ALL.

Lemma rb3_maps : maps3_chk = true -> vm_maps V = map (den rho) ALL.
Proof.
  intros Hc. rewrite (CxOpt.maps_exact_D1 E _ _ Hlx (CXS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)).
  exact (ents3_den E TT _ _ Hc).
Qed.

(* [comment removed for export] *)
Definition ent_in_b (e : fent) : bool :=
  let '(t, off, len) := e in
  match iget t M with
  | Some rg => (to_Z (rg_lo rg) <=? to_Z off) && (to_Z off + to_Z len <=? to_Z (rg_len rg))
  | None => false
  end.

Definition mirror_chk (W : Z) : bool :=
  forallb (fun e => ent_in_b e && fent_mem e ALL) (fl_maps (fl3 L3))
  && match fl_na (fl3 L3) with [] => true | _ => false end
  && (fl_brk (fl3 L3) =? 0)%uint63
  && match iget 0%uint63 M with Some rg0 => to_Z (rg_len rg0) =? W | None => false end.

Theorem rb3_mirror W : maps3_chk = true -> mirror_chk W = true ->
  mirror rho (fl3 L3) M (erase_vm (Z_to_bv 64 W) V).
Proof.
  intros Hmaps Hc. unfold mirror_chk in Hc.
  apply andb_prop in Hc as [Hc Hr0]. apply andb_prop in Hc as [Hc Hbrk]. apply andb_prop in Hc as [Hents Hna].
  apply Uint63.eqb_spec in Hbrk. split; [|split].
  - cbn [erase_vm vm_maps]. rewrite (rb3_maps Hmaps). apply Forall_forall. intros [[t off] len] He.
    rewrite forallb_forall in Hents. pose proof (Hents _ He) as H1. apply andb_prop in H1 as [H1 H2].
    unfold ent_in_b in H1. unfold ent_ok. destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
    apply andb_prop in H1 as [Ha Hb]. apply Z.leb_le in Ha, Hb.
    exists rg. split; [reflexivity|]. split; [exact Ha|]. split; [exact Hb|].
    change (adr rho t (to_Z off), Z_to_bv 64 (to_Z len)) with (den rho (t, off, len)).
    apply in_map. exact (fent_mem_In _ _ H2).
  - destruct (fl_na (fl3 L3)); [constructor | discriminate].
  - rewrite Hbrk. destruct (iget 0%uint63 M) as [rg0|] eqn:Hg0; [|discriminate]. apply Z.eqb_eq in Hr0.
    exists rg0. split; [reflexivity|]. cbn [erase_vm vm_brk]. rewrite Hr0. apply adr0_lit. apply rho_of_0.
Qed.

(* [comment removed for export] *)
Definition is_rwlazy (am : CAP.amap) : bool := match CAP.am_kind am with CAP.KRWLAZY => true | _ => false end.

Definition lazy3_chk : bool :=
  forallb (fun e => (0 <? to_Z (snd e)) && fent_mem e ALL
                    && existsb (fun am => is_rwlazy am && ent_chk3 TT am e) (CAP.a_maps CS)) (fl_lazy L3).

Theorem rb3_lazy_pw : lazy3_chk = true -> lazy_pw rho (m_vm_lazy m) (fl_lazy L3).
Proof.
  intros Hc e p He Hal Hlo Hhi. unfold lazy3_chk in Hc. rewrite forallb_forall in Hc.
  pose proof (Hc e He) as H1. apply andb_prop in H1 as [_ H1]. apply existsb_exists in H1 as (am & Ham & H2).
  apply andb_prop in H2 as [Hk Hd]. pose proof (ent_chk3_den E TT am e Hd) as Eden.
  pose proof (proj1 (Forall_forall _ _) (CXS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham) as Hkind.
  cbv beta in Hkind. unfold is_rwlazy in Hk. destruct (CAP.am_kind am); try discriminate.
  specialize (Hkind eq_refl p).
  assert (Hr : bv_unsigned (AX2.edenot E (CAP.am_base am)) <= bv_unsigned p
               < bv_unsigned (AX2.edenot E (CAP.am_base am)) + bv_unsigned (AX2.edenot E (CAP.am_len am))).
  { unfold e_hi, e_lo, e_sz in Hlo, Hhi. rewrite <- Eden in Hlo, Hhi. unfold CXS.amap_den in Hlo, Hhi. cbn [fst snd] in Hlo, Hhi. lia. }
  destruct (Hkind Hr) as [_ Hlz]. rewrite (page_base_aligned_id p Hal) in Hlz. exact Hlz.
Qed.

Theorem rb3_lazy_cov : lazy3_chk = true -> lazy_cov ALL (fl_lazy L3).
Proof.
  intros Hc. unfold lazy3_chk in Hc. rewrite forallb_forall in Hc. apply Forall_forall. intros e He.
  pose proof (Hc e He) as H1. apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [Hp Hin]. apply Z.ltb_lt in Hp.
  split; [exact Hp|]. exists e. split; [exact (fent_mem_In _ _ Hin) | apply ent_within_refl].
Qed.

Lemma rb3_wf : Forall (fun q => e_hi q <= 2 ^ 64) (vm_noaccess V) /\ Forall (fun q => e_hi q <= 2 ^ 64) (m_vm_lazy m).
Proof.
  destruct (CXS.co_wf _ _ _ _ _ _ _ _ _ _ _ _ HCS) as (_ & Hna & Hlz & _).
  split; apply Forall_forall; intros q Hq; [exact (Hna q Hq) | exact (Hlz q Hq)].
Qed.

(* [comment removed for export] *)
Definition top3_chk : bool :=
  forallb (fun p => match cls classes (fst p) with
                    | Some RCTop => top_delta TT (fst p) + to_Z (rg_len (snd p)) <=? 0
                    | _ => true
                    end) (ielements M).

Theorem rb3_hi : top3_chk = true ->
  forall x : word, argH E x = true ->
    alloc_top V <= bv_unsigned x /\ no_region rho M (bv_unsigned x).
Proof.
  intros Htop x Hx. destruct (argH_high E x Hx) as [Hceil Hisp].
  destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp _].
  destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 _]. unfold CAP.CEIL in *.
  assert (Hat : alloc_top V = ISP - 8388608) by (unfold alloc_top, stack_max_size; rewrite Eisp; lia).
  split; [lia|]. intros t rg Hg Hin. unfold in_ival in Hin.
  destruct (reg3_get A CS TT classes M t rg Hregs Hg) as (c & Ecl & Hcl & Hlt & _).
  destruct (HM t rg Hg) as (_ & _ & Hnw & _).
  pose proof (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT t _ _ c Hcl Hnw _ Hin) as Hsem.
  unfold regs3_chk, span_ok_chk in Hregs. apply andb_prop in Hregs as [Hsp Hall]. apply andb_prop in Hsp as [_ Hih]. apply Z.leb_le in Hih.
  destruct c as [| |i|]; cbn [class_sem] in Hsem.
  - unfold span_lo in Hih. lia.
  - (* [comment removed for export] *)
    unfold top3_chk in Htop. rewrite forallb_forall in Htop.
    pose proof (Htop (t, rg) (proj2 (ielements_spec M t rg) Hg)) as H1. cbn [fst snd] in H1. rewrite Ecl in H1.
    apply Z.leb_le in H1.
    rewrite (class_top_rho segs A Lim SINV argH ISP FS0 E CS R FULL m HCS TT t _ _ Hcl) in Hin. lia.
  - destruct Hsem as (p & am & Hp & _ & _ & Hxp).
    pose proof (proj1 (Forall_forall _ _) (CXS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ (nth_error_In _ _ Hp)) as Hb.
    cbv beta in Hb. unfold e_hi, e_sz, e_lo in Hxp. lia.
  - unfold span_hi in Hsem. lia.
Qed.

End Root2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ShZ.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Variable TT : ttab_e.
Hypothesis HTT : tt_wf TT = true.
Variable M : itrie region.
Variable L3 : fledger3.

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).
Local Notation kn := (CAP.kn CS).
Local Notation Mr := (CXS.Mr A argH E CS m FULL).
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.

Lemma shz_kn : AX2S.know_ok segs E Mr kn.
Proof. exact (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Definition zone_in (zlo zhi : Z) (am : CAP.amap) : bool :=
  match CAP.am_base am, CAP.am_len am, CAP.am_kind am with
  | AX2.ELit b, AX2.ELit l, CAP.KRWLAZY => (0 <=? b) && (b <=? zlo) && (zhi <=? b + l) && (b + l <? 2 ^ 64) && (0 <=? l)
  | _, _, _ => false
  end.

Definition zones_chk : bool :=
  existsb (zone_in lsh_lo lsh_hi) (CAP.a_maps CS) && existsb (zone_in hsh_lo hsh_hi) (CAP.a_maps CS).

Lemma zone_in_facts zlo zhi am : In am (CAP.a_maps CS) -> zone_in zlo zhi am = true ->
  forall x : word, zlo <= bv_unsigned x < zhi ->
    CXS.in_ivs (bv_unsigned x) (vm_maps V) = true
    /\ CXS.in_ivs (bv_unsigned x) (vm_noaccess V) = false
    /\ page_in_ranges (page_base x) (m_vm_lazy m) = true.
Proof.
  intros Ham Hz x Hx. unfold zone_in in Hz.
  destruct (CAP.am_base am) as [b| | | | | | |] eqn:Eb; try discriminate.
  destruct (CAP.am_len am) as [l| | | | | | |] eqn:El; try discriminate.
  destruct (CAP.am_kind am) eqn:Ek; try discriminate.
  apply andb_prop in Hz as [Hz H5]. apply andb_prop in Hz as [Hz H4]. apply andb_prop in Hz as [Hz H3]. apply andb_prop in Hz as [H1 H2].
  apply Z.leb_le in H1, H2, H3, H5. apply Z.ltb_lt in H4.
  pose proof (proj1 (Forall_forall _ _) (CXS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HCS) am Ham) as Hkind. cbv beta in Hkind.
  rewrite Eb, El in Hkind. cbn [AX2.edenot] in Hkind. rewrite (br_lit_small b), (br_lit_small l) in Hkind by lia.
  destruct (Hkind Ek x ltac:(lia)) as [Hna Hlz]. split; [|split; assumption].
  apply in_ivs_true. exists (CXS.amap_den E am). split.
  - rewrite (CxOpt.maps_exact_D1 E _ _ Hlx (CXS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HCS)). apply in_map. exact Ham.
  - unfold e_hi, e_sz, e_lo, CXS.amap_den. cbn [fst snd]. rewrite Eb, El. cbn [AX2.edenot].
    rewrite (br_lit_small b), (br_lit_small l) by lia. lia.
Qed.

Lemma zones_facts : zones_chk = true -> forall x : word, in_shadow (bv_unsigned x) ->
    CXS.in_ivs (bv_unsigned x) (vm_maps V) = true
    /\ CXS.in_ivs (bv_unsigned x) (vm_noaccess V) = false
    /\ page_in_ranges (page_base x) (m_vm_lazy m) = true.
Proof.
  unfold zones_chk. intros Hc x Hx. apply andb_prop in Hc as [H1 H2].
  apply existsb_exists in H1 as (am1 & Ha1 & Hz1). apply existsb_exists in H2 as (am2 & Ha2 & Hz2).
  destruct Hx as [Hx|Hx]; [exact (zone_in_facts _ _ am1 Ha1 Hz1 x Hx) | exact (zone_in_facts _ _ am2 Ha2 Hz2 x Hx)].
Qed.

(* [comment removed for export] *)
Definition zapart (p : AX2.expr * AX2.expr) : bool :=
  match len_hi kn (snd p) with
  | Some h => AX2.ranges_apart kn (AX2.ELit 0) span_lo (span_hi - span_lo) (fst p) 0 h
  | None => false
  end.

Lemma zapart_span p z : zapart p = true -> span_lo <= z < span_hi ->
  ~ (CXS.uE E (fst p) <= z < CXS.uE E (fst p) + CXS.uE E (snd p)).
Proof.
  unfold zapart. intros Hc Hz Hin. destruct (len_hi kn (snd p)) as [h|] eqn:Hl; [|discriminate].
  pose proof (len_hi_sound segs E kn _ FULL shz_kn (snd p) h Hl) as Hh. unfold AX2S.elenZ in Hh.
  pose proof (AX2S.ranges_apart_sound segs E _ kn _ _ _ _ _ _ shz_kn Hc) as D1.
  unfold AX2S.estart in D1. cbn [AX2.a_base AX2.a_off AX2.edenot] in D1.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in D1. unfold CXS.uE in Hin. lia.
Qed.

Lemma zapart_sound p z : zapart p = true -> in_shadow z ->
  ~ (CXS.uE E (fst p) <= z < CXS.uE E (fst p) + CXS.uE E (snd p)).
Proof.
  intros Hc Hz. apply (zapart_span p z Hc). unfold in_shadow, lsh_lo, lsh_hi, hsh_lo, hsh_hi, span_lo, span_hi in *. lia.
Qed.

(* [comment removed for export] *)
Definition sh_region_chk (sb : AX2.expr) (sk : Z) (sn : AX2.expr) : bool :=
  match aview [] M [] (xt_of TT) (AX2.SA sb sk), len_hi kn sn with
  | Some (t, o), Some h =>
      match iget t M with
      | Some rg => (to_Z (rg_lo rg) <=? o) && (o + h <=? to_Z (rg_len rg))
      | None => false
      end
  | _, _ => false
  end.

Definition sh_exempt_chk (b n : AX2.expr) : bool :=
  existsb (fun e : fent => let '(t, off, len) := e in
                           CAP.xinsideJ kn b 0 n (tte TT t) (to_Z off) (AX2.ELit (to_Z len))) (fl_ex L3).

Definition sh_kzero_q (sb : AX2.expr) (sk : Z) (sn : AX2.expr) (K : AX2.kentry) : bool :=
  match K with
  | AX2.KZero a nz => CAP.xinsideJ kn sb sk sn (AX2.a_base a) (AX2.a_off a) nz
  | _ => false
  end.
(* [comment removed for export] *)
Definition sh_kzero_chk (sb : AX2.expr) (sk : Z) (sn : AX2.expr) : bool :=
  if existsb (sh_kzero_q sb sk sn)
       (List.filter (fun K => match K with AX2.KZero a _ => AX2.expr_eqb (AX2.a_base a) sb | _ => false end) kn)
  then true else existsb (sh_kzero_q sb sk sn) kn.
Lemma sh_kzero_chk_ex sb sk sn : sh_kzero_chk sb sk sn = true ->
  existsb (fun K => match K with
                    | AX2.KZero a nz => CAP.xinsideJ kn sb sk sn (AX2.a_base a) (AX2.a_off a) nz
                    | _ => false
                    end) kn = true.
Proof.
  unfold sh_kzero_chk. intros Hc.
  destruct (existsb (sh_kzero_q sb sk sn)
              (List.filter (fun K => match K with AX2.KZero a _ => AX2.expr_eqb (AX2.a_base a) sb | _ => false end) kn)) eqn:Ef; [|exact Hc].
  apply existsb_exists in Ef as (K & HK & Hq). apply List.filter_In in HK as [HK _]. apply existsb_exists. exists K. split; [exact HK | exact Hq].
Qed.

Definition sh_cover_chk (p : AX2.expr * AX2.expr) : bool :=
  let '(sb, sk, sn) := CAP.shadow_of A kn (fst p) (snd p) in
  CAP.flat_x kn sb sk sn && (3 <=? AX2.ealign kn (fst p))
  (* [comment removed for export] *)
  && (if (if sh_region_chk sb sk sn then true else sh_exempt_chk (fst p) (snd p)) then true else sh_kzero_chk sb sk sn).

Definition shz_chk : bool :=
  (CAP.shadow_off A =? to_Z shadow_K) && (CAP.img_hi A <=? lsh_lo) && zones_chk
  && forallb zapart (CAP.a_vis CS) && forallb zapart (CAP.a_ghost CS)
  && forallb sh_cover_chk (CAP.a_vis CS).

Lemma shz_zones : shz_chk = true -> zones_chk = true.
Proof.
  unfold shz_chk. intros Hc. do 3 (apply andb_prop in Hc as [Hc _]). apply andb_prop in Hc as [_ Hz]. exact Hz.
Qed.

Lemma div8_facts ub un k : 0 <= ub -> 0 <= un -> 3 <= k -> (2 ^ k | ub) ->
  ub mod 8 = 0 /\ (ub + un) / 8 = ub / 8 + un / 8.
Proof.
  intros Hub Hun Hk [q Hq].
  assert (E8 : 2 ^ k = 2 ^ (k - 3) * 8) by (replace k with ((k - 3) + 3) at 1 by lia; rewrite Z.pow_add_r by lia; reflexivity).
  assert (Hm : ub mod 8 = 0) by (rewrite Hq, E8, Z.mul_assoc; apply Z.mod_mul; lia).
  split; [exact Hm|]. clear - Hm Hub Hun. Z.div_mod_to_equations. lia.
Qed.

Theorem rb3_ShZ : shz_chk = true ->
  forall x : word, in_shadow (bv_unsigned x) -> no_region rho M (bv_unsigned x) ->
    ~ exempted rho (fl_ex L3) (bv_unsigned x) ->
    rview segs FULL x = Some (Z_to_bv 8 0) /\ wview segs FULL x <> None.
Proof.
  unfold shz_chk. intros Hc x Hz Hnr Hnex.
  apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hgh]. apply andb_prop in Hc as [Hc Hvis].
  apply andb_prop in Hc as [Hc Hzones]. apply andb_prop in Hc as [HK Hih]. apply Z.eqb_eq in HK. apply Z.leb_le in Hih.
  destruct (zones_facts Hzones x Hz) as (Hmaps & Hna & Hlz).
  assert (Hzero : FULL x = Some (Z_to_bv 8 0)).
  { destruct (CXS.hid A argH E CS m x) eqn:Eh.
    - apply (CXS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HCS x Eh Hmaps Hna Hlz).
      unfold CXS.in_ghost. apply not_true_is_false. intros Hg. apply existsb_exists in Hg as (p & Hp & Hin).
      rewrite forallb_forall in Hgh. apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
      exact (zapart_sound p _ (Hgh p Hp) Hz (conj I1 I2)).
    - unfold CXS.hid in Eh. apply orb_false_iff in Eh as [_ Ev]. apply negb_false_iff in Ev.
      unfold CXS.vis in Ev. cbv zeta in Ev.
      assert (Hh : CXS.in_hull A (bv_unsigned x) = false).
      { unfold CXS.in_hull. apply andb_false_iff. right. apply Z.ltb_ge. unfold in_shadow, lsh_lo, hsh_lo in *. lia. }
      assert (Ht : (alloc_top V <=? bv_unsigned x) = false).
      { apply Z.leb_gt. destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 _]. unfold CAP.CEIL in Htop1.
        unfold in_shadow, lsh_hi, hsh_hi in Hz. lia. }
      rewrite Hh, Ht in Ev. cbn [orb] in Ev. apply andb_prop in Ev as [_ Ev]. rewrite Hlz in Ev. cbn [negb orb] in Ev.
      unfold CXS.in_allow in Ev. apply orb_prop in Ev as [Ev|Ev].
      + exfalso. unfold CXS.in_vis in Ev. apply existsb_exists in Ev as (p & Hp & Hin).
        rewrite forallb_forall in Hvis. apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
        exact (zapart_sound p _ (Hvis p Hp) Hz (conj I1 I2)).
      + unfold CXS.in_sh in Ev. apply existsb_exists in Ev as (p & Hp & Hin).
        apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
        unfold CXS.sh_lo in I1. unfold CXS.sh_hi in I2. rewrite HK in I1, I2.
        rewrite forallb_forall in Hcov. pose proof (Hcov p Hp) as Hcp. unfold sh_cover_chk in Hcp.
        destruct (CAP.shadow_of A kn (fst p) (snd p)) as [[sb sk] sn] eqn:Esh.
        apply andb_prop in Hcp as [Hcp Hways]. apply andb_prop in Hcp as [Hflat Hal]. apply Z.leb_le in Hal.
        assert (Hshok : CXS.shadow_ok A) by (unfold CXS.shadow_ok; rewrite HK; change (to_Z shadow_K) with 2147450880; lia).
        destruct (CXS.shadow_of_val segs A Hshok E Mr kn (fst p) (snd p) sb sk sn shz_kn Esh Hflat) as [Est Eln].
        rewrite HK in Est.
        destruct (AX2S.ealign_sound segs E Mr kn (fst p) shz_kn) as [_ Hdiv].
        unfold CXS.uE in I1, I2.
        set (ub := bv_unsigned (AX2.edenot E (fst p))) in *. set (un := bv_unsigned (AX2.edenot E (snd p))) in *.
        pose proof (br_u64 (AX2.edenot E (fst p))) as Hub. fold ub in Hub.
        pose proof (br_u64 (AX2.edenot E (snd p))) as Hun. fold un in Hun.
        destruct (div8_facts ub un _ ltac:(lia) ltac:(lia) Hal Hdiv) as [Hm8 Hsplit].
        rewrite Hsplit in I2.
        assert (Est' : AX2S.estart E (AX2.SA sb sk) = ub / 8 + to_Z shadow_K).
        { rewrite Est. apply Z.mod_small. change (to_Z shadow_K) with 2147450880.
          assert (ub / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
          assert (0 <= ub / 8) by (apply Z.div_pos; lia). lia. }
        apply orb_prop in Hways as [Hways|Hkz]; [apply orb_prop in Hways as [Hrg|Hex]|].
        * (* [comment removed for export] *)
          exfalso. unfold sh_region_chk in Hrg.
          destruct (aview [] M [] (xt_of TT) (AX2.SA sb sk)) as [[t o]|] eqn:Hav; [|discriminate].
          destruct (len_hi kn sn) as [h|] eqn:Hl; [|discriminate].
          destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
          apply andb_prop in Hrg as [R1 R2]. apply Z.leb_le in R1, R2.
          pose proof (len_hi_sound segs E kn _ FULL shz_kn sn h Hl) as Hh2. rewrite Eln in Hh2.
          pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M [] (xt_of TT) HM (rho_of_0 TT E) eq_refl (xt_of_ok TT E HTT) _ t o Hav) as Hs.
          rewrite env_eta in Hs. rewrite Est' in Hs.
          apply (Hnr t rg Hg). unfold in_ival. lia.
        * (* [comment removed for export] *)
          exfalso. apply Hnex. unfold sh_exempt_chk in Hex. apply existsb_exists in Hex as ([[t off] len] & He & Hxi).
          destruct (CXS.xinsideJ_sound segs E Mr kn _ _ _ _ _ _ shz_kn Hxi) as [X1 X2].
          unfold AX2S.estart, AX2S.elenZ in X1, X2. cbn [AX2.a_base AX2.a_off AX2.edenot] in X1, X2.
          rewrite <- (rho_tte E TT t) in X1, X2. fold ub in X1, X2. fold un in X2.
          pose proof (i63_range len) as Hlen. pose proof (i63_range off) as Hoff. pose proof (br_u64 (rho t)) as Hrt.
          rewrite (br_lit_small (to_Z len)) in X2 by lia.
          exists (t, off, len), (8 * (bv_unsigned x - to_Z shadow_K)). split; [exact He|].
          assert (Elo : e_lo (den rho (t, off, len)) = bv_unsigned (rho t) + to_Z off).
          { unfold e_lo. cbn [den fst]. apply adr_unsigned; lia. }
          assert (Ehi : e_hi (den rho (t, off, len)) = bv_unsigned (rho t) + to_Z off + to_Z len).
          { unfold e_hi. rewrite Elo, (e_sz_den rho (t, off, len)). reflexivity. }
          rewrite Elo, Ehi. split.
          -- clear - I1 I2 X1 X2 Hm8 Hub Hun. Z.div_mod_to_equations. lia.
          -- rewrite Z.mul_comm, Z.div_mul by lia. lia.
        * (* [comment removed for export] *)
          apply sh_kzero_chk_ex in Hkz. apply existsb_exists in Hkz as (K & HKin & HKc).
          destruct K as [ | a nz | | | | | | | | ]; try discriminate.
          destruct a as [ab ao]. cbn [AX2.a_base AX2.a_off] in HKc.
          destruct (CXS.xinsideJ_sound segs E Mr kn _ _ _ _ _ _ shz_kn HKc) as [X1 X2].
          rewrite Est', Eln in X2. rewrite Est' in X1.
          pose proof (proj1 (Forall_forall _ _) shz_kn _ HKin) as Hok. cbn [AX2S.kentry_ok] in Hok. destruct Hok as [_ Hbytes].
          specialize (Hbytes (bv_unsigned x - AX2S.estart E (AX2.SA ab ao)) ltac:(lia)).
          replace (AX2S.estart E (AX2.SA ab ao) + (bv_unsigned x - AX2S.estart E (AX2.SA ab ao))) with (bv_unsigned x) in Hbytes by lia.
          rewrite Z_to_bv_bv_unsigned in Hbytes. unfold CXS.Mr, mrestrict in Hbytes.
          destruct (CXS.hid A argH E CS m x); [discriminate | exact Hbytes]. }
  split; [unfold rview; rewrite Hzero; reflexivity | unfold wview; rewrite Hzero; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zq_chk (p : int) (plo phi : Z) (q : AX2.expr * AX2.expr) : bool :=
  (3 <=? AX2.ealign kn (fst q))
  && (if match len_hi kn (snd q) with
         | Some h => AX2.ranges_apart kn (tte TT p) plo (phi - plo) (fst q) 0 h
         | None => false
         end
      then true
      else let '(sb, sk, sn) := CAP.shadow_of A kn (fst q) (snd q) in CAP.flat_x kn sb sk sn && sh_kzero_chk sb sk sn).

(* [comment removed for export] *)
Definition zsh_chkB (p : int) (plo phi blo bhi : Z) : bool :=
  (CAP.shadow_off A =? to_Z shadow_K) && (CAP.img_hi A <=? lsh_lo) && zones_chk
  && forallb zapart (CAP.a_vis CS) && forallb zapart (CAP.a_ghost CS)
  && (plo mod 8 =? 0) && (phi mod 8 =? 0) && (0 <=? plo) && (plo <=? phi)
  && (3 <=? AX2.ealign kn (tte TT p))
  && (((bhi + phi <=? span_lo) || (span_hi <=? blo + plo)) && (bhi + phi <=? 2 ^ 47))
  && forallb (zq_chk p plo phi) (CAP.a_vis CS).

(* [comment removed for export] *)
Definition zsh_pre : bool :=
  (CAP.shadow_off A =? to_Z shadow_K) && (CAP.img_hi A <=? lsh_lo) && zones_chk
  && forallb zapart (CAP.a_vis CS) && forallb zapart (CAP.a_ghost CS).
Definition zsh_chkP (pre : bool) (p : int) (plo phi blo bhi : Z) : bool :=
  pre
  && (plo mod 8 =? 0) && (phi mod 8 =? 0) && (0 <=? plo) && (plo <=? phi)
  && (3 <=? AX2.ealign kn (tte TT p))
  && (((bhi + phi <=? span_lo) || (span_hi <=? blo + plo)) && (bhi + phi <=? 2 ^ 47))
  && forallb (zq_chk p plo phi) (CAP.a_vis CS).
Lemma zsh_chkP_eq p plo phi blo bhi : zsh_chkP zsh_pre p plo phi blo bhi = zsh_chkB p plo phi blo bhi.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition zq_chkR (ra : ra_t) (p : int) (plo phi : Z) (q : AX2.expr * AX2.expr) : bool :=
  (3 <=? AX2.ealign kn (fst q))
  && (if match len_hi kn (snd q) with
         | Some h => ra (tte TT p) plo (phi - plo) (fst q) 0 h
         | None => false
         end
      then true
      else let '(sb, sk, sn) := CAP.shadow_of A kn (fst q) (snd q) in CAP.flat_x kn sb sk sn && sh_kzero_chk sb sk sn).
Definition zsh_chkPR (ra : ra_t) (pre : bool) (p : int) (plo phi blo bhi : Z) : bool :=
  pre
  && (plo mod 8 =? 0) && (phi mod 8 =? 0) && (0 <=? plo) && (plo <=? phi)
  && (3 <=? AX2.ealign kn (tte TT p))
  && (((bhi + phi <=? span_lo) || (span_hi <=? blo + plo)) && (bhi + phi <=? 2 ^ 47))
  && forallb (zq_chkR ra p plo phi) (CAP.a_vis CS).
Lemma zsh_chkPR_eq ra p plo phi blo bhi : ra = AX2.ranges_apart kn ->
  zsh_chkPR ra zsh_pre p plo phi blo bhi = zsh_chkB p plo phi blo bhi.
Proof. intros ->. reflexivity. Qed.

Theorem zsh_zeroB p plo phi blo bhi : zsh_chkB p plo phi blo bhi = true -> blo <= bv_unsigned (rho p) <= bhi ->
  forall x : word,
    bv_unsigned (rho p) / 8 + to_Z shadow_K + plo / 8 <= bv_unsigned x < bv_unsigned (rho p) / 8 + to_Z shadow_K + phi / 8 ->
    rview segs FULL x = Some (Z_to_bv 8 0) /\ wview segs FULL x <> None.
Proof.
  unfold zsh_chkB. intros Hc [Hblo Hbhi] x Hx.
  apply andb_prop in Hc as [Hc Hqs]. apply andb_prop in Hc as [Hc Hrng]. apply andb_prop in Hc as [Hc Halp].
  apply andb_prop in Hc as [Hc Hple]. apply andb_prop in Hc as [Hc Hp0]. apply andb_prop in Hc as [Hc Hm2]. apply andb_prop in Hc as [Hc Hm1].
  apply andb_prop in Hc as [Hc Hgh]. apply andb_prop in Hc as [Hc Hvis]. apply andb_prop in Hc as [Hc Hzones].
  apply andb_prop in Hc as [HK Hih]. apply Z.eqb_eq in HK, Hm1, Hm2. apply Z.leb_le in Hih, Hp0, Hple, Halp.
  apply andb_prop in Hrng as [Hside H47]. apply Z.leb_le in H47.
  destruct (AX2S.ealign_sound segs E Mr kn (tte TT p) shz_kn) as [_ Hdivp]. rewrite <- (rho_tte E TT p) in Hdivp.
  set (rp := bv_unsigned (rho p)) in *. set (X := bv_unsigned x) in *.
  pose proof (br_u64 (rho p)) as Hrp. fold rp in Hrp.
  destruct (div8_facts rp 0 _ ltac:(lia) ltac:(lia) Halp Hdivp) as [Hrp8 _].
  change (to_Z shadow_K) with 2147450880 in *.
  (* [comment removed for export] *)
  assert (HP : rp + plo <= 8 * (X - 2147450880) < rp + phi).
  { clear - Hx Hrp8 Hm1 Hm2. Z.div_mod_to_equations. lia. }
  assert (Hz : in_shadow X).
  { unfold in_shadow, lsh_lo, lsh_hi, hsh_lo, hsh_hi. unfold span_lo, span_hi in Hside.
    apply orb_prop in Hside as [Hs|Hs]; apply Z.leb_le in Hs; [left | right]; lia. }
  destruct (zones_facts Hzones x Hz) as (Hmaps & Hna & Hlz).
  assert (Hzero : FULL x = Some (Z_to_bv 8 0)).
  { destruct (CXS.hid A argH E CS m x) eqn:Eh.
    - apply (CXS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HCS x Eh Hmaps Hna Hlz).
      unfold CXS.in_ghost. apply not_true_is_false. intros Hg. apply existsb_exists in Hg as (q & Hq & Hin).
      rewrite forallb_forall in Hgh. apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
      exact (zapart_sound q _ (Hgh q Hq) Hz (conj I1 I2)).
    - unfold CXS.hid in Eh. apply orb_false_iff in Eh as [_ Ev]. apply negb_false_iff in Ev.
      unfold CXS.vis in Ev. cbv zeta in Ev.
      assert (Hh : CXS.in_hull A (bv_unsigned x) = false).
      { unfold CXS.in_hull. apply andb_false_iff. right. apply Z.ltb_ge. fold X. unfold in_shadow, lsh_lo, hsh_lo in *. lia. }
      assert (Ht : (alloc_top V <=? bv_unsigned x) = false).
      { apply Z.leb_gt. destruct (CXS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Htop1 _]. unfold CAP.CEIL in Htop1.
        fold X. unfold in_shadow, lsh_hi, hsh_hi in Hz. lia. }
      rewrite Hh, Ht in Ev. cbn [orb] in Ev. apply andb_prop in Ev as [_ Ev]. rewrite Hlz in Ev. cbn [negb orb] in Ev.
      unfold CXS.in_allow in Ev. apply orb_prop in Ev as [Ev|Ev].
      + exfalso. unfold CXS.in_vis in Ev. apply existsb_exists in Ev as (q & Hq & Hin).
        rewrite forallb_forall in Hvis. apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
        exact (zapart_sound q _ (Hvis q Hq) Hz (conj I1 I2)).
      + unfold CXS.in_sh in Ev. apply existsb_exists in Ev as (q & Hq & Hin).
        apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
        unfold CXS.sh_lo in I1. unfold CXS.sh_hi in I2. rewrite HK in I1, I2.
        rewrite forallb_forall in Hqs. pose proof (Hqs q Hq) as Hcq. unfold zq_chk in Hcq.
        apply andb_prop in Hcq as [Halq Hways]. apply Z.leb_le in Halq.
        destruct (AX2S.ealign_sound segs E Mr kn (fst q) shz_kn) as [_ Hdiv].
        unfold CXS.uE in I1, I2.
        set (ub := bv_unsigned (AX2.edenot E (fst q))) in *. set (un := bv_unsigned (AX2.edenot E (snd q))) in *.
        pose proof (br_u64 (AX2.edenot E (fst q))) as Hub. fold ub in Hub.
        pose proof (br_u64 (AX2.edenot E (snd q))) as Hun. fold un in Hun.
        destruct (div8_facts ub un _ ltac:(lia) ltac:(lia) Halq Hdiv) as [Hm8 Hsplit].
        rewrite Hsplit in I2. fold X in I1, I2. change (to_Z shadow_K) with 2147450880 in I1, I2.
        destruct (match len_hi kn (snd q) with
                  | Some h => AX2.ranges_apart kn (tte TT p) plo (phi - plo) (fst q) 0 h
                  | None => false end) eqn:Hap.
        * (* [comment removed for export] *)
          exfalso. destruct (len_hi kn (snd q)) as [h|] eqn:Hl; [|discriminate].
          pose proof (len_hi_sound segs E kn _ FULL shz_kn (snd q) h Hl) as Hh2. unfold AX2S.elenZ in Hh2. fold un in Hh2.
          pose proof (AX2S.ranges_apart_sound segs E _ kn _ _ _ _ _ _ shz_kn Hap) as D1.
          unfold AX2S.estart in D1. cbn [AX2.a_base AX2.a_off] in D1. rewrite <- (rho_tte E TT p) in D1. fold rp ub in D1.
          clear - D1 Hh2 I1 I2 HP Hm8 Hun. Z.div_mod_to_equations. lia.
        * (* [comment removed for export] *)
          destruct (CAP.shadow_of A kn (fst q) (snd q)) as [[sb sk] sn] eqn:Esh.
          apply andb_prop in Hways as [Hflat Hkz].
          assert (Hshok : CXS.shadow_ok A) by (unfold CXS.shadow_ok; rewrite HK; change (to_Z shadow_K) with 2147450880; lia).
          destruct (CXS.shadow_of_val segs A Hshok E Mr kn (fst q) (snd q) sb sk sn shz_kn Esh Hflat) as [Est Eln].
          rewrite HK in Est. fold ub in Est. fold un in Eln.
          assert (Est' : AX2S.estart E (AX2.SA sb sk) = ub / 8 + 2147450880).
          { rewrite Est. change (to_Z shadow_K) with 2147450880. apply Z.mod_small.
            assert (ub / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
            assert (0 <= ub / 8) by (apply Z.div_pos; lia). lia. }
          apply sh_kzero_chk_ex in Hkz. apply existsb_exists in Hkz as (K & HKin & HKc).
          destruct K as [ | a nz | | | | | | | | ]; try discriminate.
          destruct a as [ab ao]. cbn [AX2.a_base AX2.a_off] in HKc.
          destruct (CXS.xinsideJ_sound segs E Mr kn _ _ _ _ _ _ shz_kn HKc) as [X1 X2].
          rewrite Est', Eln in X2. rewrite Est' in X1.
          pose proof (proj1 (Forall_forall _ _) shz_kn _ HKin) as Hok. cbn [AX2S.kentry_ok] in Hok. destruct Hok as [_ Hbytes].
          specialize (Hbytes (bv_unsigned x - AX2S.estart E (AX2.SA ab ao)) ltac:(fold X; lia)).
          replace (AX2S.estart E (AX2.SA ab ao) + (bv_unsigned x - AX2S.estart E (AX2.SA ab ao))) with (bv_unsigned x) in Hbytes by lia.
          rewrite Z_to_bv_bv_unsigned in Hbytes. unfold CXS.Mr, mrestrict in Hbytes.
          destruct (CXS.hid A argH E CS m x); [discriminate | exact Hbytes]. }
  split; [unfold rview; rewrite Hzero; reflexivity | unfold wview; rewrite Hzero; discriminate].
Qed.

Lemma zsh_chkB_bounds p plo phi blo bhi : zsh_chkB p plo phi blo bhi = true -> blo <= bv_unsigned (rho p) <= bhi ->
  0 <= plo /\ plo <= phi /\ phi <= 2 ^ 47.
Proof.
  unfold zsh_chkB. intros Hc [_ Hbhi].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hrng]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc Hple]. apply andb_prop in Hc as [_ Hp0]. apply Z.leb_le in Hp0, Hple.
  apply andb_prop in Hrng as [_ H47]. apply Z.leb_le in H47.
  pose proof (br_u64 (rho p)). lia.
Qed.

(* [comment removed for export] *)
Definition zsh_chk (p : int) (plo phi : Z) : bool :=
  match AX2.base_range kn (tte TT p) with
  | Some (blo, bhi) => zsh_chkB p plo phi blo bhi
  | None => false
  end.

Lemma zsh_base_range p blo bhi : AX2.base_range kn (tte TT p) = Some (blo, bhi) -> blo <= bv_unsigned (rho p) <= bhi.
Proof.
  intros Hbr. destruct (AX2S.base_range_sound segs E Mr kn _ blo bhi shz_kn Hbr) as [Hblo Hbhi].
  rewrite <- (rho_tte E TT p) in Hblo, Hbhi. lia.
Qed.

Theorem zsh_zero p plo phi : zsh_chk p plo phi = true ->
  forall x : word,
    bv_unsigned (rho p) / 8 + to_Z shadow_K + plo / 8 <= bv_unsigned x < bv_unsigned (rho p) / 8 + to_Z shadow_K + phi / 8 ->
    rview segs FULL x = Some (Z_to_bv 8 0) /\ wview segs FULL x <> None.
Proof.
  unfold zsh_chk. destruct (AX2.base_range kn (tte TT p)) as [[blo bhi]|] eqn:Hbr; [|discriminate]. intros Hc.
  exact (zsh_zeroB p plo phi blo bhi Hc (zsh_base_range p blo bhi Hbr)).
Qed.

Lemma zsh_chk_bounds p plo phi : zsh_chk p plo phi = true -> 0 <= plo /\ plo <= phi /\ phi <= 2 ^ 47.
Proof.
  unfold zsh_chk. destruct (AX2.base_range kn (tte TT p)) as [[blo bhi]|] eqn:Hbr; [|discriminate]. intros Hc.
  exact (zsh_chkB_bounds p plo phi blo bhi Hc (zsh_base_range p blo bhi Hbr)).
Qed.

End ShZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RootAll.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.

Variable TT : ttab_e.
Variable n : int.
Variable shapes : list rshape.
Variable cuts : list (int * list Z).
Variable classes : list (int * rclass).
Variable CS : CAP.acs.
Variable d : sdesc.
Variable bs : list ditem.
Variable L3 : fledger3.
Variable W : Z.

Local Notation M0d := (f_mem (dress (state_of d) bs)).
Local Notation R0 := (segments_reserved segs).

(* [comment removed for export] *)
Definition lit_ivs : list (Z * Z) :=
  flat_map (fun e : fent => let '(t, off, len) := e in if (t =? 0)%uint63 then [(to_Z off, to_Z off + to_Z len)] else []) (fl_all L3).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ord_rng_chk (ta tb : int) (dd : Z) : bool :=
  match AX2.base_range (CAP.kn CS) (tte TT ta), AX2.base_range (CAP.kn CS) (tte TT tb) with
  | Some (_, ahi), Some (blo, _) => (ahi + dd <=? blo)
  | _, _ => false
  end.

Definition ord_chk (o : int * int * Z) : bool :=
  let '(ta, tb, dd) := o in
  (to_Z ta <? to_Z n) && (to_Z tb <? to_Z n)
  && (if CAP.xinsideJ (CAP.kn CS) (tte TT tb) 0 (AX2.ELit 1) (tte TT ta) dd (AX2.ELit (2 ^ 62)) then true
      else ord_rng_chk ta tb dd).

(* [comment removed for export] *)
Definition res_term (m : Z) (ka : Z * AX2.expr) : option Z :=
  let '(k, a) := ka in
  if (k mod m =? 0) then Some 0 else
  if match AX2.find_align (CAP.kn CS) a with Some q => ((k * q) mod m =? 0) | None => false end then Some 0 else
  if match AX2.find_align (CAP.kn CS) (AX2.EAlu Instr.ALU_ADD a (AX2.ELit 1)) with
     | Some q => ((k * q) mod m =? 0) && (2 ^ 64 mod q =? 0) | None => false end then Some ((- k) mod m) else None.
Fixpoint res_terms (m : Z) (ts : list (Z * AX2.expr)) : option Z :=
  match ts with
  | [] => Some 0
  | ka :: r => match res_term m ka, res_terms m r with Some x, Some y => Some (x + y) | _, _ => None end
  end.
Definition res_root_chk (o : int * Z * Z) : bool :=
  let '(t, m, c) := o in
  (to_Z t <? to_Z n) && (0 <? m) && (2 ^ 64 mod m =? 0)
  && match res_terms m (snd (AX2.lin_of (tte TT t))) with
     | Some r => ((fst (AX2.lin_of (tte TT t)) + r) mod m =? c)
     | None => false
     end.

Definition synt3_chk : bool :=
  coverZ lit_ivs (Datatypes.S (length (fl_all L3))) span_lo span_hi
  && forallb (fun e => (0 <? to_Z (snd e)) && fent_mem e (fl_all L3)) (fl_ex L3)
  && forallb (fun e => fent_mem e (fl_maps (fl3 L3)) || (fent_tag e =? 0)%uint63
                       || match iget (fent_tag e) M0d with None => true | Some _ => false end) (fl_all L3)
  && forallb (fun e => to_Z (fent_tag e) <? to_Z n) (fl_all L3 ++ fl_allow L3)
  && match fl_ops L3 with [] => true | _ => false end
  && forallb ord_chk (fl_ord L3)
  && match fl_allow L3 with [] => true | _ => false end
  && (CAP.a_abytes CS <=? fl_Ab L3)
  && (CAP.a_eager CS <=? fl_E L3) && (fl_E L3 + fl_Ab L3 <=? Lim)
  && forallb res_root_chk (fl_res L3).     (* [comment removed for export] *)

Definition root3_chk : bool :=
  CAP.no_fog (CAP.a_maps CS)
  && led_chk segs A CS W (fl_c (fl3 L3)) (fl_S (fl3 L3))
  && regs3_chk A CS TT classes M0d
  && maps3_chk CS TT L3 && mirror_chk M0d L3 W && lazy3_chk CS TT L3
  && top3_chk TT classes M0d
  && shz_chk A CS TT M0d L3
  && synt3_chk.

Lemma root3_parts : root3_chk = true ->
  CAP.no_fog (CAP.a_maps CS) = true /\ res_chk segs A = true /\ maps3_chk CS TT L3 = true
  /\ Forall (fun e => to_Z (fent_tag e) < to_Z n) (fl_all L3) /\ fl_ops L3 = [] /\ fl_allow L3 = []
  /\ shz_chk A CS TT M0d L3 = true /\ regs3_chk A CS TT classes M0d = true.
Proof.
  unfold root3_chk. intros Hc.
  apply andb_prop in Hc as [Hc Hsynt]. apply andb_prop in Hc as [Hc Hshz]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hmaps].
  apply andb_prop in Hc as [Hc Hregs]. apply andb_prop in Hc as [Hnf Hled].
  assert (Hres : res_chk segs A = true) by (unfold led_chk in Hled; do 7 (apply andb_prop in Hled as [Hled _]); exact Hled).
  unfold synt3_chk in Hsynt. apply andb_prop in Hsynt as [Hsynt _].
  apply andb_prop in Hsynt as [Hs _]. apply andb_prop in Hs as [Hs _]. apply andb_prop in Hs as [Hs _].
  apply andb_prop in Hs as [Hs Hallow]. apply andb_prop in Hs as [Hs _]. apply andb_prop in Hs as [Hs Hops].
  apply andb_prop in Hs as [Hs Htags]. 
  split; [exact Hnf|]. split; [exact Hres|]. split; [exact Hmaps|]. split.
  - rewrite forallb_forall in Htags. apply Forall_forall. intros e He. apply Z.ltb_lt. apply Htags. apply in_or_app. left. exact He.
  - split; [destruct (fl_ops L3); [reflexivity | discriminate]|]. split; [destruct (fl_allow L3); [reflexivity | discriminate]|].
    split; [exact Hshz | exact Hregs].
Qed.

Variable E : AX2.env.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
(* [comment removed for export] *)
Hypothesis HTT : tt_wf TT = true.
Hypothesis HRn0 : Rn segs IM n (rho_of TT E) (state_of d)
                     (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).
Hypothesis Hdlt : Forall (ditem_lt n) bs.
Hypothesis Hdok : Forall (ditem_ok (rho_of TT E)) bs.
Hypothesis Hroot : root3_chk = true.

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).
Local Notation ms0 := (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).

(* [comment removed for export] *)
Local Notation A0 := (CXS.allowA A E CS).

Lemma res_odd_aux mo k q u w : 0 < mo -> 0 < q -> (k * q) mod mo = 0 -> 2 ^ 64 mod q = 0 ->
  (exists z, w = u + 1 + z * 2 ^ 64) -> w mod q = 0 -> (k * u) mod mo = (- k) mod mo.
Proof.
  intros Hm Hq Hkq H64 [z Hz] Hw.
  apply Z.mod_divide in Hkq; [|lia]. destruct Hkq as [j Hj].
  apply Z.mod_divide in H64; [|lia]. destruct H64 as [s Hs].
  apply Z.mod_divide in Hw; [|lia]. destruct Hw as [t Ht].
  assert (Eu : k * u = - k + ((t - z * s) * j) * mo).
  { assert (u = (t - z * s) * q - 1) by (rewrite Hs in Hz; lia). subst u.
    replace (k * ((t - z * s) * q - 1)) with (- k + (t - z * s) * (k * q)) by ring. rewrite Hj. ring. }
  rewrite Eu. apply Z.mod_add. lia.
Qed.

Lemma res_odd_den a : exists z, bv_unsigned (AX2.edenot E (AX2.EAlu Instr.ALU_ADD a (AX2.ELit 1))) = AX2S.uE E a + 1 + z * 2 ^ 64.
Proof.
  change (AX2.edenot E (AX2.EAlu Instr.ALU_ADD a (AX2.ELit 1))) with (alu64 Instr.ALU_ADD (AX2.edenot E a) (Z_to_bv 64 1)).
  destruct (AX2S.u_add_eqm (AX2.edenot E a) (Z_to_bv 64 1)) as [z Hz]. exists z. rewrite Hz. unfold AX2S.uE.
  rewrite (br_lit_small 1) by lia. reflexivity.
Qed.

Lemma res_term_sound mo ka r : 0 < mo -> res_term mo ka = Some r -> (fst ka * AX2S.uE E (snd ka)) mod mo = r mod mo.
Proof.
  intros Hm. destruct ka as [k a]. unfold res_term. cbn [fst snd].
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
  destruct (k mod mo =? 0) eqn:E0.
  { intros Hr. injection Hr as <-. apply Z.eqb_eq in E0. rewrite <- Z.mul_mod_idemp_l by lia. rewrite E0. reflexivity. }
  destruct (AX2.find_align (CAP.kn CS) a) as [q|] eqn:Ea.
  - destruct ((k * q) mod mo =? 0) eqn:E1.
    + intros Hr. injection Hr as <-. apply Z.eqb_eq in E1.
      destruct (AX2S.find_align_sound segs E _ _ a q Hkn Ea) as [Hq Hd]. unfold AX2S.uE.
      apply Z.mod_divide in Hd; [|lia]. destruct Hd as [s Hs]. rewrite Hs.
      replace (k * (s * q)) with (s * (k * q)) by ring. rewrite <- Z.mul_mod_idemp_r by lia. rewrite E1, Z.mul_0_r. reflexivity.
    + destruct (AX2.find_align (CAP.kn CS) (AX2.EAlu Instr.ALU_ADD a (AX2.ELit 1))) as [q'|] eqn:Eb; [|discriminate].
      destruct (((k * q') mod mo =? 0) && (2 ^ 64 mod q' =? 0)) eqn:E2; [|discriminate].
      intros Hr. injection Hr as <-. apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E2, E3.
      destruct (AX2S.find_align_sound segs E _ _ _ q' Hkn Eb) as [Hq Hd].
      rewrite Z.mod_mod by lia. exact (res_odd_aux mo k q' (AX2S.uE E a) _ Hm Hq E2 E3 (res_odd_den a) Hd).
  - destruct (AX2.find_align (CAP.kn CS) (AX2.EAlu Instr.ALU_ADD a (AX2.ELit 1))) as [q'|] eqn:Eb; [|discriminate].
    destruct (((k * q') mod mo =? 0) && (2 ^ 64 mod q' =? 0)) eqn:E2; [|discriminate].
    intros Hr. injection Hr as <-. apply andb_prop in E2 as [E2 E3]. apply Z.eqb_eq in E2, E3.
    destruct (AX2S.find_align_sound segs E _ _ _ q' Hkn Eb) as [Hq Hd].
    rewrite Z.mod_mod by lia. exact (res_odd_aux mo k q' (AX2S.uE E a) _ Hm Hq E2 E3 (res_odd_den a) Hd).
Qed.

Lemma res_terms_sound mo : 0 < mo -> forall ts r, res_terms mo ts = Some r -> AX2S.tden E ts mod mo = r mod mo.
Proof.
  intros Hm. induction ts as [|ka ts IH]; intros r Hr; cbn [res_terms AX2S.tden] in *.
  - injection Hr as <-. reflexivity.
  - destruct (res_term mo ka) as [x|] eqn:Ex; [|discriminate]. destruct (res_terms mo ts) as [y|] eqn:Ey; [|discriminate].
    injection Hr as <-. destruct ka as [k a]. pose proof (res_term_sound mo (k, a) x Hm Ex) as H1. cbn [fst snd] in H1.
    rewrite Z.add_mod by lia. rewrite H1, (IH y eq_refl). rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma res_root_sound o : res_root_chk o = true -> res_ok n rho o.
Proof.
  destruct o as [[t mo] c]. unfold res_root_chk, res_ok. cbn [fst snd]. intros Hc.
  apply andb_prop in Hc as [Hc Hr]. apply andb_prop in Hc as [Hc H64]. apply andb_prop in Hc as [Ht Hm].
  apply Z.ltb_lt in Ht, Hm. apply Z.eqb_eq in H64.
  destruct (res_terms mo (snd (AX2.lin_of (tte TT t)))) as [r|] eqn:Er; [|discriminate]. apply Z.eqb_eq in Hr.
  split; [exact Ht|]. split; [exact Hm|].
  rewrite (rho_tte E TT t). destruct (AX2S.lin_of_sound E (tte TT t)) as [q Hq]. unfold AX2S.lden in Hq. fold (AX2S.uE E (tte TT t)).
  pose proof (res_terms_sound mo Hm _ _ Er) as Hts.
  apply Z.mod_divide in H64; [|lia]. destruct H64 as [s Hs].
  assert (Eu : AX2S.uE E (tte TT t) = fst (AX2.lin_of (tte TT t)) + AX2S.tden E (snd (AX2.lin_of (tte TT t))) - q * s * mo) by (rewrite Hq; rewrite Hs; ring).
  rewrite Eu. rewrite Z.add_mod in Hr by lia. rewrite <- Hts in Hr. rewrite <- Z.add_mod in Hr by lia.
  rewrite <- Hr. unfold Z.sub. rewrite <- Z.mul_opp_l. rewrite Z.mod_add by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Variable XA : list fent.
Definition xa_bytes : Z := fold_right (fun e acc => to_Z (snd e) + 8192 + acc) 0 XA.
Definition xa_root_chk : bool := (CAP.a_abytes CS + xa_bytes <=? fl_Ab L3).
Local Notation A0X := (map (denA rho) XA ++ A0).

Lemma lz_A_bytes_app (a b : list (Z * Z)) : LazyCfg.A_bytes (a ++ b) = LazyCfg.A_bytes a + LazyCfg.A_bytes b.
Proof. induction a as [|iv a IH]; [reflexivity|]. cbn [app LazyCfg.A_bytes fold_right]. fold (LazyCfg.A_bytes (a ++ b)). fold (LazyCfg.A_bytes a). lia. Qed.

Lemma lz_A_bytes_cons iv (a : list (Z * Z)) : LazyCfg.A_bytes (iv :: a) = Z.max 0 (snd iv - fst iv) + LazyCfg.A_bytes a.
Proof. reflexivity. Qed.

Lemma xa_bytes_bound_gen : forall l : list fent,
  LazyCfg.A_bytes (map (denA rho) l) <= fold_right (fun e acc => to_Z (snd e) + 8192 + acc) 0 l.
Proof.
  induction l as [|[[t off] len] r IH]; [cbn; lia|].
  cbn [map fold_right]. rewrite lz_A_bytes_cons. cbn [snd].
  set (S1 := LazyCfg.A_bytes (map (denA rho) r)) in *.
  pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range off) as Ho. pose proof (i63_range len) as Hl.
  unfold denA. cbn [fst snd]. unfold pg_dn, pg_upZ.
  set (x := bv_unsigned (rho t) + to_Z off) in *.
  assert (H1 : x / 4096 * 4096 <= x < x / 4096 * 4096 + 4096) by (clear; Z.div_mod_to_equations; lia).
  assert (H2 : (x + to_Z len + 4095) / 4096 * 4096 <= x + to_Z len + 4095) by (clear; Z.div_mod_to_equations; lia).
  lia.
Qed.

Lemma xa_bytes_bound : LazyCfg.A_bytes (map (denA rho) XA) <= xa_bytes.
Proof. exact (xa_bytes_bound_gen XA). Qed.

Lemma page_allowedb_app_r (A1 A2 : list (Z * Z)) p : LazyCfg.page_allowedb A2 p = true -> LazyCfg.page_allowedb (A1 ++ A2) p = true.
Proof.
  unfold LazyCfg.page_allowedb. intros H. apply existsb_exists in H as (iv & Hin & Hc). apply existsb_exists.
  exists iv. split; [apply in_or_app; right; exact Hin | exact Hc].
Qed.

Hypothesis HXA : xa_root_chk = true.
Hypothesis HLZX : LZ IM rho (m_vm_lazy m) A0X (f_mem (state_of d)).

(* [comment removed for export] *)
Lemma root3_lx : CxOpt.ledger_exact E (CAP.a_maps CS).
Proof.
  pose proof Hroot as Hc. unfold root3_chk in Hc.
  do 7 (apply andb_prop in Hc as [Hc _]). apply andb_prop in Hc as [Hnf Hled].
  exact (led_lx segs A Lim SINV argH ISP FS0 E CS R FULL m _ _ _ HCS Hnf Hled).
Qed.

Theorem rb_DInv3_genX :
  DInv3 cfg segs IM R0 Lim [] FULL (fun _ _ => True) [] bvmap_empty (Z_to_bv 32 0) (PropExec.seg_rom segs)
        (fun x => argH E x = true) (Z_to_bv 64 W) (vm_noaccess V) (m_vm_lazy m) (vm_brk V) A0X
        n rho (dress (state_of d) bs) L3 ms0 m.
Proof.
  unfold root3_chk in Hroot.
  apply andb_prop in Hroot as [Hc Hsynt]. apply andb_prop in Hc as [Hc Hshz]. apply andb_prop in Hc as [Hc Htop].
  apply andb_prop in Hc as [Hc Hlazy]. apply andb_prop in Hc as [Hc Hmir]. apply andb_prop in Hc as [Hc Hmaps].
  apply andb_prop in Hc as [Hc Hregs]. apply andb_prop in Hc as [Hnf Hled].
  pose proof (led_lx segs A Lim SINV argH ISP FS0 E CS R FULL m _ _ _ HCS Hnf Hled) as Hlx.     (* [comment removed for export] *)
  pose proof (Rn_dress segs IM n rho (state_of d) ms0 bs HRn0 Hdlt Hdok) as HRn0d.
  assert (HR0d : FxRel.R segs IM rho (dress (state_of d) bs) ms0) by (apply HRn0d; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR0d) as Hmem. cbn [ms_mem PropExec.mkst] in Hmem.
  assert (HM : forall t rg, iget t M0d = Some rg -> region_ok rho t rg) by (intros t rg Hg; exact (proj1 (proj1 Hmem t rg Hg))).
  assert (Hres : res_chk segs A = true).
  { unfold led_chk in Hled. do 7 (apply andb_prop in Hled as [Hled _]). exact Hled. }
  unfold synt3_chk in Hsynt.
  apply andb_prop in Hsynt as [Hsynt Hres0].
  apply andb_prop in Hsynt as [Hs HLim]. apply andb_prop in Hs as [Hs HE]. apply andb_prop in Hs as [Hs HAbc].
  apply andb_prop in Hs as [Hs Hallow]. apply andb_prop in Hs as [Hs Hord]. apply Z.leb_le in HAbc.
  destruct (fl_allow L3) as [|al0 allow0] eqn:Eallow; [|discriminate].
  pose proof (CXS.A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E CS) as HAwf.
  assert (Eal : allowed A0X rho L3 = A0X) by (unfold allowed; rewrite Eallow; reflexivity).
  unfold xa_root_chk in HXA. apply Z.leb_le in HXA. pose proof xa_bytes_bound as HXb.
  pose proof (CXS.co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hab0.
  apply andb_prop in Hs as [Hs Hops]. apply andb_prop in Hs as [Hs Htags]. apply andb_prop in Hs as [Hs Hclass].
  apply andb_prop in Hs as [Hcov Hex]. apply Z.leb_le in HLim, HE.
  destruct (fl_ops L3) as [|o0 ops0] eqn:Eops; [|discriminate].
  pose proof (rb3_maps segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT L3 Hmaps) as Emaps.
  split; [|split; [|split]].
  - (* [comment removed for export] *)
    split; [exact HRn0d|]. split; [exact (rho_of_0 TT E)|].
    split; [rewrite erase_halted; exact (CXS.co_halt _ _ _ _ _ _ _ _ _ _ _ _ HCS)|].
    split; [apply erase_nolazy|]. rewrite erase_vmmaps.
    split; [exact (rb3_ledger_inv segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx W _ _ Hled)|].
    split; [exact (rb3_regions_covered segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT classes M0d HM Hres _ Hregs)|].
    split; [exact (rb3_mirror segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT M0d L3 W Hmaps Hmir)|].
    split; [exact I|]. split; [exact I|]. split; [intros t []|]. intros t [].
  - (* [comment removed for export] *)
    destruct (rb3_wf segs A Lim SINV argH ISP FS0 E CS R FULL m HCS) as [Hwna Hwlz].
    constructor.
    + rewrite Eal. destruct (page_inv_of_MInv A0 m HAwf (CXS.co_minv _ _ _ _ _ _ _ _ _ _ _ _ HCS)) as [P1 P2 P3 P4].
      constructor; [exact P1 | exact P2 | | ].
      * eapply Forall_impl; [|exact P3]. intros p Hp. exact (page_allowedb_app_r _ _ p Hp).
      * rewrite lz_A_bytes_app, (A_bytes_wf A0 HAwf). pose proof (CXS.co_limit _ _ _ _ _ _ _ _ _ _ _ _ HCS) as HL0.   (* [comment removed for export] *)
        pose proof (CXS.co_eager _ _ _ _ _ _ _ _ _ _ _ _ HCS) as He0. unfold AsanAcct.eager_used in He0. unfold LazyCfg.eager_used. lia.
    + rewrite Eal.
      apply (LZ_same IM rho _ _ _ _ (dress_same bs (f_mem (state_of d)))). exact HLZX.
    + exact (rb3_lazy_pw segs A Lim SINV argH ISP FS0 E CS R FULL m HCS TT L3 Hlazy).
    + unfold FxDrive3.mat_lazy. apply Forall_forall. intros p Hp.
      exact (AsanAcct.minv_lazy _ _ (CXS.co_minv _ _ _ _ _ _ _ _ _ _ _ _ HCS) p Hp).
    + exact (rb3_lazy_cov CS TT L3 Hlazy).
    + rewrite Eal, lz_A_bytes_app, (A_bytes_wf A0 HAwf). lia.
    + exact (CXS.co_limit _ _ _ _ _ _ _ _ _ _ _ _ HCS).
    + exact Emaps.
    + rewrite Eops. reflexivity.
    + rewrite Eops. reflexivity.
    + unfold mirror_chk in Hmir. do 3 (apply andb_prop in Hmir as [Hmir _]). rewrite forallb_forall in Hmir.
      apply Forall_forall. intros e He. pose proof (Hmir e He) as H1. apply andb_prop in H1 as [_ H1]. exact (fent_mem_In _ _ H1).
    + rewrite forallb_forall in Hclass. apply Forall_forall. intros e He. pose proof (Hclass e He) as H1.
      apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
      * left. exact (fent_mem_In _ _ H1).
      * right. left. apply Uint63.eqb_spec in H1. exact H1.
      * right. right. destruct (iget (fent_tag e) M0d); [discriminate | reflexivity].
    + rewrite Eops, Eallow. cbn [map app]. rewrite app_nil_r. rewrite forallb_forall in Htags. apply Forall_forall. intros e He.
      apply Z.ltb_lt. apply Htags. rewrite ?Eallow, app_nil_r. exact He.
    + pose proof (CXS.co_eager _ _ _ _ _ _ _ _ _ _ _ _ HCS) as He. unfold AsanAcct.eager_used in He. unfold LazyCfg.eager_used. lia.
    + exact HLim.
    + exact Hwna.
    + exact Hwlz.
    + rewrite Eops. intros o x p [].
    + rewrite forallb_forall in Hord. apply Forall_forall. intros [[ta tb] dd] Ho. pose proof (Hord _ Ho) as Hoc.
      unfold ord_chk in Hoc. apply andb_prop in Hoc as [Hoc Hx]. apply andb_prop in Hoc as [O1 O2]. apply Z.ltb_lt in O1, O2.
      unfold ord_ok. cbn [fst snd]. split; [exact O1|]. split; [exact O2|].
      destruct (CAP.xinsideJ (CAP.kn CS) (tte TT tb) 0 (AX2.ELit 1) (tte TT ta) dd (AX2.ELit (2 ^ 62))) eqn:Hxi.
      * destruct (CXS.xinsideJ_sound segs E _ (CAP.kn CS) _ _ _ _ _ _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hxi) as [X1 _].
        unfold AX2S.estart in X1. cbn [AX2.a_base AX2.a_off] in X1. rewrite <- !(rho_tte E TT) in X1. lia.
      * unfold ord_rng_chk in Hx.
        destruct (AX2.base_range (CAP.kn CS) (tte TT ta)) as [[alo ahi]|] eqn:Ra; [|discriminate].
        destruct (AX2.base_range (CAP.kn CS) (tte TT tb)) as [[blo bhi]|] eqn:Rb; [|discriminate].
        apply Z.leb_le in Hx.
        destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ alo ahi (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Ra) as [_ A2].
        destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ blo bhi (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Rb) as [B1 _].
        rewrite <- (rho_tte E TT ta) in A2. rewrite <- (rho_tte E TT tb) in B1. lia.
    + rewrite Eops. constructor.
    + apply Forall_forall. intros o Ho. rewrite forallb_forall in Hres0. exact (res_root_sound o (Hres0 o Ho)).
  - (* [comment removed for export] *)
    constructor.
    + exact (rb3_ShZ segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT HTT M0d L3 HM Hshz).
    + intros x Hx. destruct (coverZ_sound _ _ _ _ Hcov x Hx) as (q & Hq & Hxq).
      unfold lit_ivs in Hq. apply in_flat_map in Hq as ([[t off] len] & He & Hq).
      destruct (t =? 0)%uint63 eqn:Et; [|destruct Hq]. destruct Hq as [<-|[]]. apply Uint63.eqb_spec in Et. subst t.
      exists (0%uint63, off, len). split; [exact He|]. split; [reflexivity|]. cbn [fst snd] in Hxq.
      pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen.
      unfold e_hi, e_lo. rewrite (e_sz_den rho (0%uint63, off, len)). cbn [den fst snd].
      rewrite (adr0_lit rho _ (rho_of_0 TT E)), (br_lit_small (to_Z off)) by lia. exact Hxq.
    + exact (rb3_span_ok segs A Lim SINV argH ISP FS0 HULL_ok E CS R FULL m HCS Hlx TT classes M0d HM Hres Hregs).
    + rewrite forallb_forall in Hex. apply Forall_forall. intros e He. pose proof (Hex e He) as H1.
      apply andb_prop in H1 as [Hp Hin]. apply Z.ltb_lt in Hp. split; [exact Hp|].
      exists e. split; [exact (fent_mem_In _ _ Hin) | apply ent_within_refl].
  - (* [comment removed for export] *)
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    intros x Hx.
    destruct (rb3_hi segs A Lim SINV argH ISP FS0 argH_high E CS R FULL m HCS Hlx TT classes M0d HM Hregs Htop x Hx) as [H1 H2].
    split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.

End RootAll.

(* [comment removed for export] *)
Theorem rb_DInv3_gen cfg segs IM A Lim SINV argH ISP FS0
  (SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None)
  (HULL_ok : CXS.hull_ok A)
  (argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a)
  TT n classes CS d bs L3 W E R FULL m :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  tt_wf TT = true ->
  Rn segs IM n (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)) ->
  Forall (ditem_lt n) bs -> Forall (ditem_ok (rho_of TT E)) bs ->
  root3_chk segs A Lim TT n classes CS d bs L3 W = true ->
  side_chk A TT (CAP.kn CS) d = true ->
  DInv3 cfg segs IM (segments_reserved segs) Lim [] FULL (fun _ _ => True) [] bvmap_empty (Z_to_bv 32 0) (PropExec.seg_rom segs)
        (fun x => argH E x = true) (Z_to_bv 64 W) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) (vm_brk (m_vmmaps m)) (CXS.allowA A E CS)
        n (rho_of TT E) (dress (state_of d) bs) L3
        (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)) m.
Proof.
  intros HCS HTT HRn0 Hdlt Hdok Hroot Hside.
  assert (HR0 : FxRel.R segs IM (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)))
    by (apply HRn0; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR0) as Hmem0. cbn [ms_mem PropExec.mkst] in Hmem0.
  pose proof (CXS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH ISP argH_high E CS m) as Hnoseg.
  pose proof (fun a => rb_hull A argH ISP HULL_ok argH_high CS E m a) as Hhull.
  pose proof (CXS.lazy_cover_cs segs A Lim (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
                HULL_ok SINV argH ISP FS0 0%nat E CS R FULL m HCS) as Hcover.
  pose proof (side_LZ segs IM A E TT (CAP.kn CS) _ FULL d _ _ HTT Hnoseg (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hhull Hcover Hmem0 Hside) as HLZ.
  refine (rb_DInv3_genX cfg segs IM A Lim SINV argH ISP FS0 HULL_ok argH_high TT n classes CS d bs L3 W
            E R FULL m HCS HTT HRn0 Hdlt Hdok Hroot [] _ HLZ).
  unfold xa_root_chk, xa_bytes. cbn [fold_right]. rewrite Z.add_0_r.
  unfold root3_chk in Hroot. apply andb_prop in Hroot as [_ Hsynt]. unfold synt3_chk in Hsynt.
  do 3 (apply andb_prop in Hsynt as [Hsynt _]). apply andb_prop in Hsynt as [_ Hab]. exact Hab.
Qed.

(* [comment removed for export] *)
Theorem rb_DInv3 cfg segs IM (HIM : image_ok segs IM) (HWR : image_wr_ok IM) A Lim SINV argH ISP FS0
  (SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None)
  (HULL_ok : CXS.hull_ok A)
  (argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a)
  TT n shapes cuts classes CS d bs L3 W E R FULL m :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  rb_check IM A TT n shapes cuts classes CS d = true ->
  forallb (dress_chk TT (CAP.kn CS) n) bs = true ->
  root3_chk segs A Lim TT n classes CS d bs L3 W = true ->
  side_chk A TT (CAP.kn CS) d = true ->
  DInv3 cfg segs IM (segments_reserved segs) Lim [] FULL (fun _ _ => True) [] bvmap_empty (Z_to_bv 32 0) (PropExec.seg_rom segs)
        (fun x => argH E x = true) (Z_to_bv 64 W) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) (vm_brk (m_vmmaps m)) (CXS.allowA A E CS)
        n (rho_of TT E) (dress (state_of d) bs) L3
        (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)) m.
Proof.
  intros HCS Hrb Hdress Hroot Hside.
  pose proof (rb_parts IM A TT n shapes cuts classes CS d Hrb) as (HTT & _).
  pose proof (rb_Rn segs IM HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high TT n shapes cuts classes CS d E R FULL m HCS Hrb) as HRn0.
  destruct (dress_chk_all segs E TT (CAP.kn CS) _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) n bs Hdress) as [Hdlt Hdok].
  eapply rb_DInv3_gen; eassumption.
Qed.
