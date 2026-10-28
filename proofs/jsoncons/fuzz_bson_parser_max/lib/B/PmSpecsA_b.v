(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceABx .
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSPA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

(* [comment removed for export] *)
Definition accA : (word -> option byte) -> Z -> Z -> Prop := fun M a n => aacc M a n.
Definition annA : (word -> option byte) -> Z -> Z -> Z -> Prop := fun M b u c => HAJ.ann_shadow M b u c.
Abbreviation vstr_at := (PM.vstr_at segs accA).
Abbreviation vec_at := (PM.vec_at segs accA annA).
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation nullis_at := (PM.nullis_at segs A accA).
Abbreviation parser_at := (PM.parser_at segs A accA annA).
Abbreviation src_fields_at := (PM.src_fields_at segs accA).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ffroomA (h : Z) (FF LK : list fframe) : Prop := forall k, In k [0; 1; 3; 5] ->      (* [comment removed for export] *) Z.of_nat (ff_count k (FF ++ LK)) + h + 2 <= ff_cap k.
Definition ffrsA (FF : list fframe) (sp : Z) : Prop := forall f, In f FF -> sp + 32 <= ff_rs f.
Definition aobjA (FF : list fframe) (o n : Z) : Prop :=
  exists f, In f FF /\ ff_addr f + 32 <= o /\ o + n <= ff_addr f + ff_bytes (ff_class f) - 8.
(* [comment removed for export] *)
Definition HV : heap_layout := LibIfaceAB.heap_view L ar.
Definition scA (c : credit) : credit := (fst c, hl_b_lin L * snd c).
Abbreviation loc_ok := (PMST.loc_ok segs A).
Abbreviation sys_ok := (PMST.sys_ok segs A).
Abbreviation err_ok := (PMSTA.err_okA segs A AA).

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model.

(* [comment removed for export] *)
Definition pm_scr (h : Z) : Z := 12288 + 2048 * h.
(* [comment removed for export] *)
Definition entryA (R : bvmap 5 word) (M : word -> option byte) (sp r h : Z) : Prop :=
  getr R 1%bv = Z_to_bv 64 r /\ L5.ra_ok r /\ getr R 2%bv = Z_to_bv 64 sp /\ getr R 3%bv = Z_to_bv 64 (pa_gp A)
  /\ getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ L5CA.astk ar M sp (pm_scr h)
  /\ shadow_zero M (sp - pm_scr h) (pm_scr h / 8).     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition frame_okA (FF : list fframe) (fb : Z) : Prop := (exists rs, In (fb, 4, rs) FF) /\ fb mod 1024 = 0.
Definition o_ec (fb : Z) : Z := fb + pa_off_ec A.
Definition o_p (fb : Z) : Z := fb + pa_off_p A.
Definition o_v (fb : Z) : Z := fb + pa_off_v A.
Definition o_is (fb : Z) : Z := fb + pa_off_is A.
Definition o_s (fb : Z) : Z := fb + pa_off_s A.
Definition o_src (fb : Z) : Z := o_p fb + 24.
Definition o_tb (fb : Z) : Z := o_p fb + 336.
Definition o_vec (fb : Z) : Z := o_p fb + 360.

(* [comment removed for export] *)
Definition credit_le (c c' : credit) : Prop := fst c <= fst c' /\ snd c <= snd c'.
Definition credit_keep (cr cr' p p' : credit) : Prop :=
  fst cr - fst p + fst p' <= fst cr' /\ snd cr - snd p + snd p' <= snd cr'.
Definition cr0 : credit := (0, 0).

(* [comment removed for export] *)
Definition ec_at (M : word -> option byte) (o v c : Z) : Prop := L5.u32_at segs M o v /\ L5.u64_at segs M (o + 8) c /\ L5.defined M o 16 /\ accA M o 16.
(* [comment removed for export] *)
Definition visitor_at (M : word -> option byte) (o : Z) : Prop := L5.u64_at segs M o (pa_vp_visitor A) /\ accA M o 8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MALLOC_SCR : Z := 4096.
Definition OPNEW_SCR : Z := 16 + MALLOC_SCR.
Definition OPDEL_SCR : Z := MALLOC_SCR.

Definition opnew_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (n sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> L5CA.astk ar M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (Aw' : list (Z * Z)) (q : Z),
        getr R' 10%bv = Z_to_bv 64 q -> regs_preserved R R' ->
        L5CA.afresh L ar LB (FF ++ LK) M' q n ->
        L5CA.ahpres L ar LB FF sp OPNEW_SCR [] M M' ->
        model_rt model model' -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ((q, n) :: LB) FF LK (adebit L cr n) Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_opnew A) M model) K.

Definition opdel_spec_at (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (q n sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    In (q, n) LB -> getr R 10%bv = Z_to_bv 64 q ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> L5CA.astk ar M sp OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (lb_remove q LB) FF sp OPDEL_SCR [] M M' ->
        model_rt model model' -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (lb_remove q LB) FF LK cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.
Definition opdel_spec : Prop := opdel_spec_at (pa_opdel A).
Definition opdel_sized_spec : Prop := opdel_spec_at (pa_opdel_sized A).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition str_count (n : Z) : Z := if Z.eqb n 23 then 26 else Z.lor n 7 + 1.
Definition str_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o ptr n sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ptr -> getr R 12%bv = Z_to_bv 64 n ->
    0 <= n < 2 ^ 26 -> aobjA FF o 24 -> o mod 8 = 0 -> L5.defined M o 24 -> accA M o 24 ->
    (n = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + n <= B + m)) -> aacc M ptr n ->
    credit_le (scA (PM.cost1 HV (n + 16))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s : PM.vstr) (cr' : credit),
        regs_preserved R R' -> vstr_at M' o s -> PM.vs_size s = n ->
        (n <= 22 -> s = PM.VShort n) -> (23 <= n -> exists p, s = PM.VLong (str_count n) n p) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 0) [(o, 24)] M M' ->
        credit_keep cr cr' (scA (PM.cost1 HV (n + 16))) cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_str_ctor A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition loc_W : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) (pa_loc_foot A).
Definition locale_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o sp r : Z) (b : bool),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 2 -> ffroomA 2 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> aobjA FF o 8 -> o mod 8 = 0 -> L5.defined M o 8 ->
    PMSTA.base_okA segs A M -> loc_ok M b ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> L5.u64_at segs M' o (pa_classic_imp A) -> loc_ok M' true ->
        L5CA.ahpres L ar LB FF sp (pm_scr 2) ((o, 8) :: (if b then [] else loc_W)) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_locale_ctor A) M model) K.

(* [comment removed for export] *)
Definition locale_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> aobjA FF o 8 -> L5.u64_at segs M o (pa_classic_imp A) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (model' : Model), regs_preserved R R' -> model_rt model model' -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK cr Aw M (vml_of model') -> srealizes segs SCFG (cfg R' r M model') K) ->   (* [comment removed for export] *)
    srealizes segs SCFG (cfg R (pa_locale_dtor A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iss_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (ois os sp r : Z) (s : PM.vstr) (b : bool),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 4 -> ffroomA 4 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 ois -> getr R 11%bv = Z_to_bv 64 os -> getr R 12%bv = Z_to_bv 64 8 ->
    aobjA FF ois 272 -> aobjA FF os 24 -> ois = os + 64 -> ois mod 8 = 0 -> os mod 8 = 0 -> L5.defined M ois 272 -> accA M ois 272 ->
    vstr_at M os s -> incl (PM.vs_own s) LB -> PM.vs_size s < 2 ^ 26 -> (forall c n p, s = PM.VLong c n p -> 23 <= n) ->
    PMSTA.base_okA segs A M -> loc_ok M b ->
    credit_le (scA (PM.cost1 HV (PM.vs_size s + 32))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.vstr) (sm : PM.strm) (cr' : credit),
        regs_preserved R R' -> iss_at M' ois s' sm -> PM.vs_size s' = PM.vs_size s ->
        PM.sm_g sm = PM.vs_data (ois + 80) s' -> PM.sm_st sm = 0 ->
        loc_ok M' true ->
        L5CA.ahpres L ar LB FF sp (pm_scr 4) ((ois, 272) :: (if b then [] else loc_W)) M M' ->
        credit_keep cr cr' (scA (PM.cost1 HV (PM.vs_size s + 32))) cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_iss_ctor A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parser_init (qc b : Z) : PM.pst :=
  PM.PST 1 0 0 (PM.SRC qc qc 0) (PM.VShort 0) 0 b 0 [PM.ps_root].
Definition reader_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb oo oa : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomA 6 FF LK -> ffrsA FF sp -> frame_okA FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_is fb) -> getr R 12%bv = Z_to_bv 64 oo -> getr R 13%bv = Z_to_bv 64 oa ->
    oo = o_p fb + 464 -> L5.defined M (o_p fb) 384 -> accA M (o_p fb) 384 -> accA M oo 32 -> L5.u64_at segs M oo (pa_vp_opts A) -> L5.u64_at segs M (oo + 8) PM.MAX_ITEMS -> L5.u32_at segs M (oo + 24) PM.MAX_DEPTH ->
    iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> loc_ok M true ->
    credit_le (scA (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (qc b : Z) (cr' : credit),
        regs_preserved R R' -> parser_at M' (o_p fb) (o_is fb) (parser_init qc b) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 6) [(o_p fb, 384)] M M' ->
        credit_keep cr cr' (scA (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own (parser_init qc b) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reader_ctor A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition syscat_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (b : bool),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    PMSTA.base_okA segs A M -> sys_ok M b ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 (pa_syscat_obj A) -> sys_ok M' true ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) (if b then [] else [(pa_syscat_guard A, 2)]) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_syscat A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pst_reset (s : PM.pst) : PM.pst :=
  PM.PST 1 0 0 (PM.p_src s)
         (match PM.p_tb s with PM.VShort _ => PM.VShort 0 | PM.VLong c _ p => PM.VLong c 0 p end) (PM.p_tg s)
         (PM.p_b s) (PM.p_k s) [PM.ps_root].
Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PM.pst),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp -> frame_okA FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> parser_at M (o_p fb) (o_is fb) s -> (1 <= length (PM.p_stk s))%nat ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> parser_at M' (o_p fb) (o_is fb) (pst_reset s) ->
        (* [comment removed for export] *)
        L5CA.ahpres L ar LBX FF sp (pm_scr 1) [(o_p fb + 8, 8); (o_tb fb, 24); (o_vec fb, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reset A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition err_W : list L5.range := [(pa_errcat_guard A, 2); (pa_atexit A, 544)].
Definition make_ec_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o v sp r : Z) (b : bool),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 v -> 1 <= v <= 64 ->
    aobjA FF o 16 -> o mod 8 = 0 -> L5.defined M o 16 -> accA M o 16 ->
    PMSTA.base_okA segs A M -> err_ok M b ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> ec_at M' o v (pa_errcat_obj A) -> err_ok M' true ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) ((o, 16) :: (if b then [] else err_W)) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_make_ec A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (os isp sbp sp r : Z) (src : PM.srcst),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 2 -> ffroomA 2 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 os -> aobjA FF os 296 -> os mod 8 = 0 ->
    src_fields_at M os isp sbp src -> nullis_at M (os + 8) -> In (PM.sr_qc src, PM.CHUNK) LB ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (lb_remove (PM.sr_qc src) LB) FF sp (pm_scr 2) [(os, 296)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (lb_remove (PM.sr_qc src) LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_src_dtor A) M model) K.

(* [comment removed for export] *)
Definition ios_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o vp rdb st sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> aobjA FF o 152 -> o mod 8 = 0 ->
    PM.iosb_at segs A accA M o vp rdb st -> PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) [(o, 152)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_ios_dtor A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_srcf (fb : Z) : list L5.range := [(o_src fb + 256, 40); (o_is fb + 40, 8); (o_is fb + 152, 4)].
Definition W_src (fb : Z) (src : PM.srcst) : list L5.range := W_srcf fb ++ [(PM.sr_qc src, PM.CHUNK)].
(* [comment removed for export] *)
Definition W_run (fb : Z) : list L5.range :=
  [(o_p fb + 8, 8)] ++ W_srcf fb ++ [(o_tb fb, 24); (o_vec fb, 24); (o_ec fb, 16)] ++ err_W.

Definition run_pre (M : word -> option byte) (fb : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool) : Prop :=
  parser_at M (o_p fb) (o_is fb) s /\ iss_at M (o_is fb) str sm /\ visitor_at M (o_v fb) /\ L5.u64_at segs M (o_p fb + 384) (o_v fb)
  /\ PMSTA.base_okA segs A M /\ err_ok M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s).

(* [comment removed for export] *)
Definition src_step (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  PM.sr_qc src' = PM.sr_qc src /\ PM.sm_eg sm' = PM.sm_eg sm /\ PM.sm_g sm <= PM.sm_g sm'
  /\ (PM.sm_st sm = 2 -> PM.sm_st sm' = 2) /\ PM.unread src' sm' <= PM.unread src sm.

(* [comment removed for export] *)
Definition push_rel (s s' : PM.pst) (sm sm' : PM.strm) : Prop :=
  PM.p_stk s' = PM.p_stk s
  \/ exists c, PM.p_stk s' = PM.p_stk s ++ [c] /\ PM.pstate_ok c /\ PM.ps_idx c = 0 /\ ~ PM.mode_bottom (PM.ps_mode c)
               /\ (PM.mode_counted (PM.ps_mode c) -> PM.unread (PM.p_src s') sm' < PM.unread (PM.p_src s) sm).

(* [comment removed for export] *)
Definition run_post (prog : bvmap 5 word -> PM.pst -> PM.pst -> PM.strm -> PM.strm -> Prop) (R' : bvmap 5 word)
           (M' : word -> option byte) (fb : Z) (s s' : PM.pst) (str : PM.vstr) (sm sm' : PM.strm) (e e' : bool) (cat : Z) : Prop :=
  run_pre M' fb s' str sm' e' /\ src_step (PM.p_src s) (PM.p_src s') sm sm' /\ (e = true -> e' = true)
  /\ (   (exists v, 1 <= v <= 64 /\ ec_at M' (o_ec fb) v (pa_errcat_obj A) /\ PM.p_more s' = 0 /\ e' = true)
      \/ (ec_at M' (o_ec fb) 0 cat /\ PM.inv s' /\ prog R' s s' sm sm')).

(* [comment removed for export] *)
Definition run_spec_r (pc h : Z) (args : bvmap 5 word -> Z -> PM.pst -> Prop)
           (prog : bvmap 5 word -> PM.pst -> PM.pst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomA h FF LK -> ffrsA FF sp -> frame_okA FF fb -> sp mod 32 = 0 ->
    args R fb s ->
    run_pre M fb s str sm e -> incl (PM.vs_own str) LBX -> PM.inv s -> ec_at M (o_ec fb) 0 cat ->
    PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (scA (PM.pot_parser HV s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        run_post prog R' M' fb s s' str sm sm' e e' cat ->
        L5CA.ahpres L ar LBX FF sp (pm_scr h) (W_run fb) M M' ->
        credit_keep cr cr' (scA (PM.pot_parser HV s)) (scA (PM.pot_parser HV s')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

(* [comment removed for export] *)
Definition run_post_d (d : Z) (prog : bvmap 5 word -> PM.pst -> PM.pst -> PM.strm -> PM.strm -> Prop) (R' : bvmap 5 word)
           (M' : word -> option byte) (fb : Z) (s s' : PM.pst) (str : PM.vstr) (sm sm' : PM.strm) (e e' : bool) (cat : Z) : Prop :=
  run_pre M' fb s' str sm' e' /\ src_step (PM.p_src s) (PM.p_src s') sm sm' /\ (e = true -> e' = true)
  /\ (   (exists v, 1 <= v <= 64 /\ ec_at M' (o_ec fb) v (pa_errcat_obj A) /\ PM.p_more s' = 0 /\ e' = true)
      \/ (ec_at M' (o_ec fb) 0 cat /\ PM.inv_d d s' /\ prog R' s s' sm sm')).
Lemma run_post_d0 prog R' M' fb s s' str sm sm' e e' cat :
  run_post_d 0 prog R' M' fb s s' str sm sm' e e' cat <-> run_post prog R' M' fb s s' str sm sm' e e' cat.
Proof.
  unfold run_post_d, run_post. rewrite (PM.inv_d0 s'). reflexivity.
Qed.
Definition run_spec_rd (pc h d : Z) (args : bvmap 5 word -> Z -> PM.pst -> Prop)
           (prog : bvmap 5 word -> PM.pst -> PM.pst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomA h FF LK -> ffrsA FF sp -> frame_okA FF fb -> sp mod 32 = 0 ->
    args R fb s ->
    run_pre M fb s str sm e -> incl (PM.vs_own str) LBX -> PM.inv_d d s -> ec_at M (o_ec fb) 0 cat ->
    PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (scA (PM.pot_parser HV s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        run_post_d d prog R' M' fb s s' str sm sm' e e' cat ->
        L5CA.ahpres L ar LBX FF sp (pm_scr h) (W_run fb) M M' ->
        credit_keep cr cr' (scA (PM.pot_parser HV s)) (scA (PM.pot_parser HV s')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition run_spec (pc h : Z) (args : bvmap 5 word -> Z -> PM.pst -> Prop)
           (prog : PM.pst -> PM.pst -> PM.strm -> PM.strm -> Prop) : Prop := run_spec_r pc h args (fun _ => prog).

(* [comment removed for export] *)
Definition args3 (R : bvmap 5 word) (fb : Z) (_ : PM.pst) : Prop :=      (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb).
Definition args_rv (R : bvmap 5 word) (fb : Z) (_ : PM.pst) : Prop :=    (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ exists t, 0 <= t < 256 /\ getr R 12%bv = Z_to_bv 64 t.

(* [comment removed for export] *)
Definition prog_value (s s' : PM.pst) (sm sm' : PM.strm) : Prop := push_rel s s' sm sm'.
Definition prog_value_strict (s s' : PM.pst) (sm sm' : PM.strm) : Prop :=
  push_rel s s' sm sm' /\ PM.unread (PM.p_src s') sm' < PM.unread (PM.p_src s) sm.
Definition prog_key (s s' : PM.pst) (sm sm' : PM.strm) : Prop :=
  PM.p_stk s' = PM.p_stk s /\ PM.unread (PM.p_src s') sm' < PM.unread (PM.p_src s) sm.
Definition prog_pop (s s' : PM.pst) (sm sm' : PM.strm) : Prop :=
  (exists top, PM.p_stk s = PM.p_stk s' ++ [top]) /\ PM.unread (PM.p_src s') sm' = PM.unread (PM.p_src s) sm.

(* [comment removed for export] *)
Definition rtv_spec : Prop := run_spec (pa_rtv A) 9 args3 prog_value_strict.
Definition read_value_spec : Prop := run_spec (pa_read_value A) 8 args_rv prog_value.
Definition read_key_spec : Prop := run_spec (pa_read_key A) 7 args3 prog_key.
Definition begin_array_spec : Prop := run_spec (pa_begin_array A) 7 args3 prog_value.
Definition begin_object_spec : Prop := run_spec (pa_begin_object A) 7 args3 prog_value.
(* [comment removed for export] *)
Definition args_end (R : bvmap 5 word) (fb : Z) (s : PM.pst) : Prop := args3 R fb s /\ (2 <= length (PM.p_stk s))%nat.
Definition end_array_spec : Prop := run_spec (pa_end_array A) 1 args_end prog_pop.
Definition end_object_spec : Prop := run_spec (pa_end_object A) 1 args_end prog_pop.

(* [comment removed for export] *)
Definition args_gl (R : bvmap 5 word) (fb : Z) (_ : PM.pst) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_ec fb).
Definition prog_len (R' : bvmap 5 word) (s s' : PM.pst) (sm sm' : PM.strm) : Prop :=
  PM.p_stk s' = PM.p_stk s /\ PM.unread (PM.p_src s') sm' < PM.unread (PM.p_src s) sm
  /\ exists len, 0 <= len < 2 ^ 64 /\ getr R' 10%bv = Z_to_bv 64 len.
Definition get_length_spec : Prop := forall d, 0 <= d <= 1 -> run_spec_rd (pa_get_length A) 5 d args_gl prog_len.

(* [comment removed for export] *)
Definition read_span_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb len : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomA 6 FF LK -> ffrsA FF sp -> frame_okA FF fb -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (o_tb fb) -> 0 <= len < 2 ^ 64 ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (o_tb fb + 1 <= ptr /\ ptr + n <= o_tb fb + 24)) ->
        L5.defined M' ptr n -> accA M' ptr n ->   (* [comment removed for export] *)
        parser_at M' (o_p fb) (o_is fb) s' -> iss_at M' (o_is fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        src_step (PM.p_src s) (PM.p_src s') sm sm' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 6) (W_srcf fb ++ [(o_tb fb, 24)]) M M' ->
        credit_keep cr cr' (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) (scA (PM.pot_text HV (PM.p_tb s') (PM.p_tg s'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_read_span A) M model) K.

(* [comment removed for export] *)
Definition prog_any (s s' : PM.pst) (sm sm' : PM.strm) : Prop := True.
Definition parse_post (M' : word -> option byte) (fb : Z) (s s' : PM.pst) (str : PM.vstr) (sm sm' : PM.strm) (e e' : bool) : Prop :=
  run_pre M' fb s' str sm' e' /\ src_step (PM.p_src s) (PM.p_src s') sm sm' /\ (e = true -> e' = true) /\ L5.defined M' (o_ec fb) 16.
Definition parse_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 10 -> ffroomA 10 FF LK -> ffrsA FF sp -> frame_okA FF fb -> sp mod 32 = 0 ->
    args3 R fb s ->
    run_pre M fb s str sm e -> incl (PM.vs_own str) LBX -> PM.inv s -> ec_at M (o_ec fb) 0 cat ->
    PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (scA (PM.pot_parser HV s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb s s' str sm sm' e e' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 10) (W_run fb) M M' ->
        credit_keep cr cr' (scA (PM.pot_parser HV s)) cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_parse A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scan_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (p n sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n -> aacc M p n -> (forall a, p <= a < p + n -> ahid Aw model (Z_to_bv 64 a) = false /\ ahid Aw model (Z_to_bv 64 (S a)) = false) ->
    (n = 0 \/ sp <= p \/ p + n <= sp - pm_scr 0) ->
    PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' -> L5.frame_but [(sp - pm_scr 0, pm_scr 0)] M M' -> mem_grows M M' -> model_rt model model' -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.
Definition validate_spec : Prop := scan_spec (pa_validate A).
Definition is_base10_spec : Prop := scan_spec (pa_is_base10 A).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition str_resize_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o n sp r tg : Z) (s : PM.vstr),
    ri_inv HI (PM.vs_own s ++ LB) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> aobjA FF o 24 -> o mod 8 = 0 ->
    vstr_at M o s -> PM.tb_ok s tg -> 0 <= n <= PM.vs_size s + PM.CHUNK -> n < 2 ^ 26 + PM.CHUNK ->
    credit_le (scA (PM.pot_text HV s tg)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.vstr) (tg' : Z) (cr' : credit),
        regs_preserved R R' -> vstr_at M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
        (n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
        L5CA.ahpres L ar LB FF sp (pm_scr 1) [(o, 24)] M M' ->
        credit_keep cr cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV s' tg')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_str_resize A) M model) K.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition no_W (R : bvmap 5 word) (W : list L5.range) : Prop := W = [].
Definition consumed (src src' : PM.srcst) (sm sm' : PM.strm) : Z := PM.unread src sm - PM.unread src' sm'.


(* [comment removed for export] *)
Definition with_src (s : PM.pst) (src' : PM.srcst) : PM.pst :=
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) src' (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xsgetn_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r ois dst : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 2 -> ffroomA 2 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 (ois + 16) -> getr R 11%bv = Z_to_bv 64 dst -> getr R 12%bv = Z_to_bv 64 PM.CHUNK ->
    aobjA FF ois 272 -> ois mod 8 = 0 ->
    iss_at M ois str sm -> PMSTA.base_okA segs A M -> incl (PM.vs_own str) LB ->
    (exists B m, In (B, m) LB /\ B <= dst /\ dst + PM.CHUNK <= B + m) -> accA M dst PM.CHUNK ->
    (dst + PM.CHUNK <= PM.sm_g sm \/ PM.sm_eg sm <= dst) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (c : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 c -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) ->
        iss_at M' ois str (PM.STRM (PM.sm_g sm + c) (PM.sm_eg sm) (PM.sm_st sm)) ->
        L5.defined M' dst c ->
        L5CA.ahpres L ar LB FF sp (pm_scr 2) [(ois + 40, 8); (dst, PM.CHUNK)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pa_xsgetn A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_spec (pc h : Z) (args : list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
           (Wx : bvmap 5 word -> list L5.range -> Prop)
           (res : bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomA h FF LK -> ffrsA FF sp -> frame_okA FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> args FF R M sp fb s -> Wx R Wextra ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M ->
    incl (PM.vs_own str) LBX ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        parser_at M' (o_p fb) (o_is fb) (with_src s src') ->
        iss_at M' (o_is fb) str sm' -> src_step (PM.p_src s) src' sm sm' ->
        res R R' M' (PM.p_src s) src' sm sm' ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (pm_scr h) (W_src fb (PM.p_src s) ++ Wextra) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

Definition no_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := True.

(* [comment removed for export] *)
Definition fill_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  getr R 11%bv = Z_to_bv 64 (PM.sr_qc (PM.p_src s)) /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK.
Definition fill_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  src' = src /\ exists c, getr R' 10%bv = Z_to_bv 64 c /\ 0 <= c <= PM.CHUNK /\ PM.sm_g sm' = PM.sm_g sm + c
    /\ (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0))
    /\ (PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2).
Definition fill_buffer_spec : Prop := src_spec (pa_fill_buffer A) 3 fill_args no_W fill_res.

(* [comment removed for export] *)
Definition peek_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  consumed src src' sm sm' = 0 /\
  (getr R' 10%bv = Z_to_bv 64 256 \/ (exists c, 0 <= c < 256 /\ getr R' 10%bv = Z_to_bv 64 c /\ 1 <= PM.sr_rem src')).
Definition peek_spec : Prop := src_spec (pa_peek A) 4 no_args no_W peek_res.

(* [comment removed for export] *)
Definition ignore_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := getr R 11%bv = Z_to_bv 64 1.
Definition ignore_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  (consumed src src' sm sm' = 1 \/ consumed src src' sm sm' = 0) /\ (1 <= PM.sr_rem src -> consumed src src' sm sm' = 1).
Definition ignore_spec : Prop := src_spec (pa_ignore A) 4 ignore_args no_W ignore_res.

(* [comment removed for export] *)
Definition read_dst (FF : list fframe) (M : word -> option byte) (sp fb : Z) (s : PM.pst) (p k : Z) : Prop :=
  (aobjA FF p k /\ k <= 8 /\ L5.defined M p k /\ aacc M p k /\ (p + k <= o_is fb \/ o_is fb + 272 <= p) /\ (p + k <= o_p fb \/ o_p fb + 384 <= p))
  \/ ((exists n, PM.p_tb s = PM.VShort n) /\ o_tb fb + 1 <= p /\ p + k <= o_tb fb + 24)
  \/ (exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + k <= q + c).
Definition read_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists p k, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 1 <= k <= PM.CHUNK /\ read_dst FF M sp fb s p k.
Definition read_W (R : bvmap 5 word) (W : list L5.range) : Prop :=
  exists p k, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 0 <= p < 2 ^ 64 /\ 0 <= k < 2 ^ 64 /\ W = [(p, k)].
Definition read_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  exists p k d, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 0 <= p < 2 ^ 64 /\ 1 <= k <= PM.CHUNK
    /\ getr R' 10%bv = Z_to_bv 64 d /\ 0 <= d <= k
    /\ consumed src src' sm sm' = d /\ L5.defined M' p d
    /\ (1 <= PM.sr_rem src -> 1 <= d) /\ (d = 0 -> PM.sr_rem src' = 0 /\ PM.sm_st sm' = 2).
Definition src_read_spec : Prop := src_spec (pa_src_read A) 4 read_args read_W read_res.


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition tbfill_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK /\
    exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + PM.CHUNK <= q + c.
Definition tbfill_W (R : bvmap 5 word) (W : list L5.range) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ 0 <= p < 2 ^ 64 /\ W = [(p, PM.CHUNK)].
Definition tbfill_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  fill_res R R' M' src src' sm sm' /\ exists p c, getr R 11%bv = Z_to_bv 64 p /\ getr R' 10%bv = Z_to_bv 64 c /\ L5.defined M' p c.
Definition fill_buffer_tb_spec : Prop := src_spec (pa_fill_buffer A) 3 tbfill_args tbfill_W tbfill_res.

(* [comment removed for export] *)
Definition srd_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb len : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 5 -> ffroomA 5 FF LK -> ffrsA FF sp -> frame_okA FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> getr R 11%bv = Z_to_bv 64 (o_tb fb) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> PM.unread (PM.p_src s) sm < 2 ^ 26 -> PM.vs_size (PM.p_tb s) + PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        consumed (PM.p_src s) (PM.p_src s') sm sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s) + d ->
        parser_at M' (o_p fb) (o_is fb) s' -> iss_at M' (o_is fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        src_step (PM.p_src s) (PM.p_src s') sm sm' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 5) (W_srcf fb ++ [(o_tb fb, 24)]) M M' ->
        credit_keep cr cr' (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) (scA (PM.pot_text HV (PM.p_tb s') (PM.p_tg s'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pa_srd_read A) M model) K.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition reader_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 11 -> ffroomA 11 FF LK -> ffrsA FF sp -> frame_okA FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_ec fb) ->
    run_pre M fb s str sm e -> incl (PM.vs_own str) LBX -> (1 <= length (PM.p_stk s))%nat -> ec_at M (o_ec fb) 0 cat ->
    PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (scA (PM.pot_parser HV (pst_reset s))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb (pst_reset s) s' str sm sm' e e' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 11) (W_run fb) M M' ->
        credit_keep cr cr' (scA (PM.pot_parser HV (pst_reset s))) cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reader_read A) M model) K.

(* [comment removed for export] *)
Definition vec_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PM.pstate),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> accA M t 8 -> L5.u64_at segs M t v ->
    aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> accA M v 24 ->
    vec_at M v b k stk -> In (b, 32 * 2 ^ k) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (lb_remove b LB) FF sp (pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (lb_remove b LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_vec_dtor A) M model) K.


End Specs.
End PMSPA.
