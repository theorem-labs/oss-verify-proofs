(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceABx PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnStatics PnStaticsA PnRun.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require LibIfaceAJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNRA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

(* [comment removed for export] *)
Abbreviation accA := PMSPA.accA.
Definition annA : (word -> option byte) -> Z -> Z -> Z -> Prop := fun M b u c => HAJ.ann_shadow M b u c.
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation vstr_at := (PM.vstr_at segs accA).
Abbreviation bparser_at := (PNM.bparser_at segs A accA annA (pa_vp_parser A)).
Abbreviation berr_ok := (PNSTA.berr_okA segs A AA AN).
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation pm_scr := PMSPA.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).
Abbreviation HV := (PMSPA.HV L ar).
(* [comment removed for export] *)
Definition FCB : list Z := [0; 1; 3; 5].
Abbreviation ffroomB := (PGSA.ffroomB FCB).
(* [comment removed for export] *)
Definition frame_okB (FF : list fframe) (fb : Z) : Prop := (exists rs, In (fb, 5, rs) FF) /\ fb mod 2048 = 0.

(* [comment removed for export] *)
Definition o_p (fb : Z) : Z := PMSP.o_p A fb.
Definition o_is (fb : Z) : Z := PMSP.o_is A fb.
Definition o_v (fb : Z) : Z := PMSP.o_v A fb.
Definition o_ec (fb : Z) : Z := PMSP.o_ec A fb.
Definition o_src (fb : Z) : Z := o_p fb + PNM.OFF_SRC.
Definition o_bb (fb : Z) : Z := o_p fb + PNM.OFF_BB.
Definition o_nb (fb : Z) : Z := o_p fb + PNM.OFF_NB.
Definition o_tb (fb : Z) : Z := o_p fb + PNM.OFF_TB.
Definition o_stk (fb : Z) : Z := o_p fb + PNM.OFF_STK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bmode_bottom (m : Z) : Prop := m = 0 \/ m = 1.
Definition bmode_cont (m : Z) : Prop := m = 2 \/ m = 3 \/ m = 4.
Definition bstack_shape (stk : list PNM.bstate) : Prop :=
  (1 <= length stk)%nat /\ Z.of_nat (length stk) <= PNM.MAX_DEPTH + 1
  /\ bmode_bottom (PNM.bs_mode (nth 0 stk PNM.bs_root))
  /\ (forall i, (1 <= i < length stk)%nat -> bmode_cont (PNM.bs_mode (nth i stk PNM.bs_root)))
  /\ (forall i, (i < length stk)%nat -> PNM.bstate_ok (nth i stk PNM.bs_root)).
Definition binv (s : PNM.bpst) : Prop :=      (* [comment removed for export] *)
  PNM.b_done s = 0 /\ bstack_shape (PNM.b_stk s).
Definition bflag (stk : list PNM.bstate) : Z :=
  let m := PNM.bs_mode (last stk PNM.bs_root) in if (Z.eqb m 0 || Z.eqb m 4)%bool then 1 else 0.
Definition bmu (s : PNM.bpst) (sm : PM.strm) : Z := 2 * PM.unread (PNM.b_src s) sm + bflag (PNM.b_stk s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pot_bstack (k : Z) : credit :=
  (HeapIface.hl_k_per_malloc HV * (11 - k), PNM.BSZ * (2 ^ 12 - 2 ^ (k + 1)) + (11 - k) * HeapIface.hl_b_overhead HV).
Definition pot_bparser (s : PNM.bpst) : credit :=
  PM.credit_add (pot_bstack (PNM.b_sk s))
    (PM.credit_add (PM.pot_text HV (PNM.b_tb s) (PNM.b_tg s))
       (PM.credit_add (PM.pot_text HV (PNM.b_nb s) (PNM.b_ng s)) (PGV8.pot_v8 HV (PNM.b_bb s) (PNM.b_bg s)))).

(* [comment removed for export] *)
Definition pot_callB (n : Z) : credit :=
  PM.credit_add (PM.credit_add (PM.cost1 HV (n + 16)) (PM.cost1 HV (n + 32)))
    (PM.credit_add (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV PNM.BSZ))
       (PM.credit_add (pot_bstack 0)
          (PM.credit_add (PM.pot_text HV (PM.VShort 0) 0) (PM.credit_add (PM.pot_text HV (PM.VShort 0) 0) (PGV8.pot_v8 HV PGV8.V8Null 0))))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition brun_pre (M : word -> option byte) (fb : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  bparser_at M (o_p fb) (o_is fb) s /\ iss_at M (o_is fb) str sm /\ PMSPA.visitor_at segs A M (o_v fb)
  /\ L5.u64_at segs M (o_p fb + PNM.PSIZE) (o_v fb) /\ accA M (o_p fb) (PNM.PSIZE + 8) /\ PMSTA.base_okA segs A M /\ berr_ok M ax /\ PNM.bgrow_ok s.
Definition W_brun (fb : Z) : list L5.range :=
  [(o_p fb + 8, 8)] ++ PGS.W_srcfG (o_src fb) (o_is fb) ++ [(o_bb fb, 24); (o_nb fb, 24); (o_tb fb, 24); (o_stk fb, 24); (o_ec fb, 16)]
  ++ PNST.berr_W A AN.
(* [comment removed for export] *)
Definition btop_pos (s s' : PNM.bpst) : Prop :=
  exists l c c', PNM.b_stk s = l ++ [c] /\ PNM.b_stk s' = l ++ [c'] /\ PNM.bstate_ok c'
                 /\ PNM.bs_mode c' = PNM.bs_mode c /\ PNM.bs_len c' = PNM.bs_len c /\ PNM.bs_type c' = PNM.bs_type c /\ PNM.bs_idx c' = PNM.bs_idx c.
(* [comment removed for export] *)
Definition bpush_rel (s s' : PNM.bpst) (sm sm' : PM.strm) : Prop :=
  btop_pos s s'
  \/ exists c, PNM.b_stk s' = PNM.b_stk s ++ [c] /\ PNM.bstate_ok c /\ bmode_cont (PNM.bs_mode c) /\ PNM.bs_idx c = 0
               /\ PM.unread (PNM.b_src s') sm' + 4 <= PM.unread (PNM.b_src s) sm.
Definition bprog := bvmap 5 word -> (word -> option byte) -> PNM.bpst -> PNM.bpst -> PM.strm -> PM.strm -> Prop.
(* [comment removed for export] *)
Definition bb_room (s : PNM.bpst) (sm : PM.strm) : Prop := PGV8.v8_room (PNM.b_bb s) (PM.unread (PNM.b_src s) sm).
Definition bb_post (bb : bool) (s s' : PNM.bpst) (sm sm' : PM.strm) : Prop :=
  if bb then (bb_room s sm -> PNM.b_more s' = 1 -> bb_room s' sm') else PNM.b_bb s' = PNM.b_bb s.
Definition brun_post (bb : bool) (prog : bprog) (R' : bvmap 5 word)
           (M' : word -> option byte) (fb : Z) (s s' : PNM.bpst) (str : PM.vstr) (sm sm' : PM.strm) (ax ax' : PNST.bax) (cat e : Z) : Prop :=
  brun_pre M' fb s' str sm' ax' /\ PMSP.src_step (PNM.b_src s) (PNM.b_src s') sm sm' /\ PNST.bax_le ax ax'
  /\ (   (exists v, 1 <= v <= 64 /\ PMSPA.ec_at segs M' (o_ec fb) v (pa_errcat_obj A) /\ PNM.b_more s' = 0 /\ PNST.bax_cat ax' = true
                     /\ (length (PNM.b_stk s) <= length (PNM.b_stk s'))%nat /\ binv s')   (* [comment removed for export] *)
      \/ (PMSPA.ec_at segs M' (o_ec fb) e cat /\ binv s' /\ prog R' M' s s' sm sm'))      (* [comment removed for export] *)
  /\ bb_post bb s s' sm sm'.

Definition brun_spec (bb : bool) (pc h : Z) (args : bvmap 5 word -> Z -> PNM.bpst -> PM.strm -> Prop) (prog : bprog) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomB h FF LK -> ffrsA FF sp -> frame_okB FF fb -> sp mod 32 = 0 ->
    args R fb s sm ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> binv s -> PMSPA.ec_at segs M (o_ec fb) e cat -> 0 <= e <= 64 ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 ->
    PMSP.credit_le (PMSPA.scA L (pot_bparser s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        brun_post bb prog R' M' fb s s' str sm sm' ax ax' cat e ->
        L5CA.ahpres L ar LBX FF sp (pm_scr h) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (pot_bparser s)) (PMSPA.scA L (pot_bparser s')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
(* [comment removed for export] *)
Definition brun_spec_fb (bb : bool) (fb pc h : Z) (args : bvmap 5 word -> Z -> PNM.bpst -> PM.strm -> Prop) (prog : bprog) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomB h FF LK -> ffrsA FF sp -> frame_okB FF fb -> sp mod 32 = 0 ->
    args R fb s sm ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> binv s -> PMSPA.ec_at segs M (o_ec fb) e cat -> 0 <= e <= 64 ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 ->
    PMSP.credit_le (PMSPA.scA L (pot_bparser s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        brun_post bb prog R' M' fb s s' str sm sm' ax ax' cat e ->
        L5CA.ahpres L ar LBX FF sp (pm_scr h) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (pot_bparser s)) (PMSPA.scA L (pot_bparser s')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Lemma brun_spec_iff bb pc h args prog : brun_spec bb pc h args prog <-> forall fb, brun_spec_fb bb fb pc h args prog.
Proof.
  unfold brun_spec, brun_spec_fb. split.
  - intros H fb fx R M model K LBX FF LK Aw cr sp r cat e. exact (H fx R M model K LBX FF LK Aw cr sp r fb cat e).
  - intros H fx R M model K LBX FF LK Aw cr sp r fb cat e. exact (H fb fx R M model K LBX FF LK Aw cr sp r cat e).
Qed.

(* [comment removed for export] *)
Definition bargs3 (R : bvmap 5 word) (fb : Z) (_ : PNM.bpst) (_ : PM.strm) : Prop :=      (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb).
Definition bargs_rv (R : bvmap 5 word) (fb : Z) (s : PNM.bpst) (sm : PM.strm) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ (exists t, 0 <= t < 256 /\ getr R 12%bv = Z_to_bv 64 t) /\ bb_room s sm.
Definition bargs_en (R : bvmap 5 word) (fb : Z) (_ : PNM.bpst) (_ : PM.strm) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ (getr R 12%bv = Z_to_bv 64 0 \/ getr R 12%bv = Z_to_bv 64 1).
Definition bargs_end (R : bvmap 5 word) (fb : Z) (s : PNM.bpst) (sm : PM.strm) : Prop := bargs3 R fb s sm /\ (2 <= length (PNM.b_stk s))%nat.
(* [comment removed for export] *)
Definition bcs_str (w : Z) (s : PNM.bpst) : PM.vstr := if Z.eqb w 0 then PNM.b_nb s else PNM.b_tb s.
Definition bcs_off (w : Z) : Z := if Z.eqb w 0 then PNM.OFF_NB else PNM.OFF_TB.
Definition bargs_cs (w : Z) (R : bvmap 5 word) (fb : Z) (s : PNM.bpst) (sm : PM.strm) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_p fb + bcs_off w) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb)
  /\ PM.vs_size (bcs_str w s) + PM.unread (PNM.b_src s) sm <= 2 ^ 26.
Definition bargs_rs (R : bvmap 5 word) (fb : Z) (_ : PNM.bpst) (_ : PM.strm) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_ec fb).

(* [comment removed for export] *)
Definition bprog_value : bprog := fun R' M' s s' sm sm' => bpush_rel s s' sm sm'.
Definition bprog_name : bprog := fun R' M' s s' sm sm' =>
  btop_pos s s' /\ PM.unread (PNM.b_src s') sm' < PM.unread (PNM.b_src s) sm.
Definition bprog_pop : bprog := fun R' M' s s' sm sm' =>      (* [comment removed for export] *)
  (exists l c top c', PNM.b_stk s = l ++ [c; top] /\ PNM.b_stk s' = l ++ [c'] /\ PNM.bstate_ok c'
                      /\ PNM.bs_mode c' = PNM.bs_mode c /\ PNM.bs_len c' = PNM.bs_len c
                      /\ PNM.bs_type c' = PNM.bs_type c /\ PNM.bs_idx c' = PNM.bs_idx c)
  /\ PM.unread (PNM.b_src s') sm' = PM.unread (PNM.b_src s) sm.
(* [comment removed for export] *)
Definition bprog_cs (w : Z) : bprog := fun R' M' s s' sm sm' =>
  btop_pos s s' /\ PM.unread (PNM.b_src s') sm' < PM.unread (PNM.b_src s) sm
  /\ PM.vs_size (bcs_str w s') + PM.unread (PNM.b_src s') sm' + 1 <= PM.vs_size (bcs_str w s) + PM.unread (PNM.b_src s) sm.
(* [comment removed for export] *)
Definition bprog_rs (fb : Z) : bprog := fun R' M' s s' sm sm' =>
  btop_pos s s' /\ PM.unread (PNM.b_src s') sm' + 5 <= PM.unread (PNM.b_src s) sm
  /\ exists ptr n, getr R' 10%bv = Z_to_bv 64 ptr /\ getr R' 11%bv = Z_to_bv 64 n /\ 0 <= n < 2 ^ 26 /\ L5.defined M' ptr n /\ accA M' ptr n
       /\ ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own s') ptr n \/ (o_tb fb + 1 <= ptr /\ ptr + n <= o_tb fb + 24)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition begin_document_spec : Prop := brun_spec false (PNL.pn_begin_document AN) 7 bargs3 bprog_value.
Definition begin_array_spec : Prop := brun_spec false (PNL.pn_begin_array AN) 7 bargs3 bprog_value.
(* [comment removed for export] *)
Definition end_document_spec : Prop := brun_spec false (PNL.pn_end_document AN) 3 bargs_end bprog_pop.
Definition end_array_spec : Prop := brun_spec false (PNL.pn_end_array AN) 3 bargs_end bprog_pop.
Definition read_e_name_spec : Prop := brun_spec false (PNL.pn_read_e_name AN) 6 bargs_en bprog_name.
Definition read_value_spec : Prop := brun_spec true (PNL.pn_read_value AN) 8 bargs_rv bprog_value.
Definition read_cstring_spec : Prop := forall w, (w = 0 \/ w = 1) -> brun_spec false (PNL.pn_read_cstring AN) 5 (bargs_cs w) (bprog_cs w).
Definition read_string_spec : Prop := forall fb, brun_spec_fb false fb (PNL.pn_read_string AN) 7 bargs_rs (bprog_rs fb).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition parse_post (M' : word -> option byte) (fb : Z) (s s' : PNM.bpst) (str : PM.vstr) (sm sm' : PM.strm) (ax ax' : PNST.bax) : Prop :=
  brun_pre M' fb s' str sm' ax' /\ PMSP.src_step (PNM.b_src s) (PNM.b_src s') sm sm' /\ PNST.bax_le ax ax' /\ L5.defined M' (o_ec fb) 16.
Definition parse_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat e : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 10 -> ffroomB 10 FF LK -> ffrsA FF sp -> frame_okB FF fb -> sp mod 32 = 0 ->
    bargs3 R fb s sm ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> binv s -> PMSPA.ec_at segs M (o_ec fb) e cat -> 0 <= e <= 64 ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 -> bb_room s sm ->
    PMSP.credit_le (PMSPA.scA L (pot_bparser s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb s s' str sm sm' ax ax' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 10) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (pot_bparser s)) (PMSPA.scA L PMSP.cr0) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_parse AN) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bparser_init (qc b : Z) : PNM.bpst :=
  PNM.BPST 1 0 (PM.SRC qc qc 0) PGV8.V8Null (PM.VShort 0) (PM.VShort 0) 0 0 0 b 0 [PNM.bs_root].
Definition reader_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb oo oa : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomB 6 FF LK -> ffrsA FF sp -> frame_okB FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_is fb) -> getr R 12%bv = Z_to_bv 64 oo -> getr R 13%bv = Z_to_bv 64 oa ->
    aobjA FF oo 24 -> (oo + 24 <= o_p fb \/ o_p fb + PNM.PSIZE + 8 <= oo) -> oo mod 8 = 0 -> L5.defined M (o_p fb) PNM.PSIZE -> accA M (o_p fb) PNM.PSIZE -> accA M oo 24 ->
    L5.u64_at segs M oo (pa_vp_opts A) -> L5.u32_at segs M (oo + 16) PNM.MAX_DEPTH ->
    iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> PMST.loc_ok segs A M true ->
    PMSP.credit_le (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV PNM.BSZ))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (qc b : Z) (cr' : credit),
        regs_preserved R R' -> bparser_at M' (o_p fb) (o_is fb) (bparser_init qc b) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 6) [(o_p fb, PNM.PSIZE)] M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV PNM.BSZ))) (PMSPA.scA L PMSP.cr0) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own (bparser_init qc b) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_reader_ctor AN) M model) K.

(* [comment removed for export] *)
Definition vs_clear (x : PM.vstr) : PM.vstr := match x with PM.VShort _ => PM.VShort 0 | PM.VLong c _ p => PM.VLong c 0 p end.
Definition bpst_reset (s : PNM.bpst) : PNM.bpst :=
  PNM.BPST 1 0 (PNM.b_src s) (PGV8.v8_clear (PNM.b_bb s)) (vs_clear (PNM.b_nb s)) (vs_clear (PNM.b_tb s))
           (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) [PNM.bs_root].
Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PNM.bpst),
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp -> frame_okB FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> bparser_at M (o_p fb) (o_is fb) s ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> bparser_at M' (o_p fb) (o_is fb) (bpst_reset s) ->
        (* [comment removed for export] *)
        L5CA.ahpres L ar LBX FF sp (pm_scr 1) [(o_p fb + 8, 8); (o_bb fb, 24); (o_nb fb, 24); (o_tb fb, 24); (o_stk fb, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_reset AN) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition make_ec_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o v sp r : Z) (ax : PNST.bax),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 v -> 1 <= v <= 64 ->
    aobjA FF o 16 -> o mod 8 = 0 -> L5.defined M o 16 -> accA M o 16 ->
    PMSTA.base_okA segs A M -> berr_ok M ax ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> PMSPA.ec_at segs M' o v (pa_errcat_obj A) -> berr_ok M' (PNST.bax_add_cat ax) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) ((o, 16) :: (if PNST.bax_cat ax then [] else PNST.cat_W A)) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pa_make_ec A) M model) K.

(* [comment removed for export] *)
Definition str_push_back_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o c sp r tg : Z) (x : PM.vstr),
    ri_inv HI (PM.vs_own x ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 c -> 0 <= c < 256 -> aobjA FF o 24 -> o mod 8 = 0 ->
    vstr_at M o x -> PM.tb_ok x tg -> PM.vs_size x < 2 ^ 26 ->
    PMSP.credit_le (PMSPA.scA L (PM.pot_text HV x tg)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PM.vstr) (tg' : Z) (cr' : credit),
        regs_preserved R R' -> vstr_at M' o x' -> PM.vs_size x' = PM.vs_size x + 1 -> PM.tb_ok x' tg' ->
        (PM.vs_size x < PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ tg' = tg) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PM.pot_text HV x tg)) (PMSPA.scA L (PM.pot_text HV x' tg')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_str_push_back AN) M model) K.

(* [comment removed for export] *)
Definition str_push_back_short_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o sp r n : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> aobjA FF o 24 -> o mod 8 = 0 ->      (* [comment removed for export] *)
    vstr_at M o (PM.VShort n) -> n <= 21 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> vstr_at M' o (PM.VShort (n + 1)) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) [(o, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_str_push_back AN) M model) K.

(* [comment removed for export] *)
Definition from_int_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o v sp r n : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 2 -> ffroomB 2 FF LK -> ffrsA FF sp -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> getr R 11%bv = Z_to_bv 64 o -> aobjA FF o 24 -> o mod 8 = 0 ->
    vstr_at M o (PM.VShort n) -> 0 <= n <= 11 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (n' : Z),
        regs_preserved R R' -> vstr_at M' o (PM.VShort n') -> n + 1 <= n' <= n + 11 ->
        L5CA.ahpres L ar LB FF sp (pm_scr 2) [(o, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_from_int AN) M model) K.

(* [comment removed for export] *)
Definition dec128_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (first vp sp r : Z) (ax : PNST.bax),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 3 -> ffroomB 3 FF LK -> ffrsA FF sp -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 first -> getr R 11%bv = Z_to_bv 64 (first + 42) -> getr R 12%bv = Z_to_bv 64 vp ->
    (exists B m, In (B, m) LB /\ B <= first /\ first + 42 <= B + m) -> L5.defined M first 42 ->
    aobjA FF vp 16 -> L5.defined M vp 16 -> accA M vp 16 -> accA M first 42 -> vp mod 8 = 0 ->
    PMSTA.base_okA segs A M -> berr_ok M ax ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (ptr : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> first <= ptr <= first + 42 ->
        L5.defined M' first 42 -> berr_ok M' (PNST.bax_add_dec ax) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 3) ((first, 42) :: (if PNST.bax_dec ax then [] else PNST.dec_W A AN)) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_dec128 AN) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_read_spec : Prop := PGSA.src_read_specG segs A L ar HI FCB.
Definition fill_buffer_spec : Prop := PGSA.fill_buffer_specG segs A L ar HI FCB.
Definition fill_buffer_tb_spec : Prop := PGSA.fill_buffer_tb_specG segs A L ar HI FCB.
Definition read_span_spec : Prop := PGSA.read_span_specG segs A L ar HI FCB (pa_read_span A).
Definition srd_read_spec : Prop := PGSA.srd_read_specG segs A L ar HI FCB (pa_srd_read A).
Definition read_span_v_spec : Prop := PGV8A.read_span_v_specG segs A L ar HI FCB (PNL.pn_read_span_v AN).
Definition srd_read_v_spec : Prop := PGV8A.srd_read_v_specG segs A L ar HI FCB (PNL.pn_srd_read_v AN).
Definition vu8_resize_spec : Prop := PGV8A.vu8_resize_spec segs A L ar HI FCB (PNL.pn_vu8_resize AN).
Definition vu8_append_spec : Prop := PGV8A.vu8_append_spec segs A L ar HI FCB (PNL.pn_vu8_append AN).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reader_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax),
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 11 -> ffroomB 11 FF LK -> ffrsA FF sp -> frame_okB FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_ec fb) ->
    brun_pre M fb s str sm ax -> incl (PM.vs_own str) LBX -> PMSPA.ec_at segs M (o_ec fb) 0 cat ->
    PM.unread (PNM.b_src s) sm < 2 ^ 26 -> bb_room s sm ->
    PMSP.credit_le (PMSPA.scA L (pot_bparser (bpst_reset s))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb (bpst_reset s) s' str sm sm' ax ax' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 11) (W_brun fb) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (pot_bparser (bpst_reset s))) (PMSPA.scA L PMSP.cr0) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_reader_read AN) M model) K.

(* [comment removed for export] *)
Definition vec_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PNM.bstate),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> accA M t 8 -> L5.u64_at segs M t v ->
    aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> accA M v 24 ->
    PNM.bvec_at segs accA annA M v b k stk -> In (b, PNM.BSZ * 2 ^ k) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (lb_remove b LB) FF sp (pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (lb_remove b LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_vec_dtor AN) M model) K.

(* [comment removed for export] *)
Definition lb_remove_v8 (x : PGV8.v8) (LB : list (Z * Z)) : list (Z * Z) :=
  match x with PGV8.V8Null => LB | PGV8.V8Blk b _ _ => lb_remove b LB end.
Definition vu8_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v sp r : Z) (x : PGV8.v8),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomB 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> accA M t 8 -> L5.u64_at segs M t v ->
    aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> accA M v 24 ->
    PGV8.v8_at segs accA annA M v x -> incl (PGV8.v8_own x) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (lb_remove_v8 x LB) FF sp (pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (lb_remove_v8 x LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (PNL.pn_vu8_dtor AN) M model) K.

End Specs.
End PNRA.
