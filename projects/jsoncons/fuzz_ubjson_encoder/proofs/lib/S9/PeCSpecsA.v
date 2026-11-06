(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCStatics PeCModel PeCSinkA PeCStaticsA PeCModelA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSPA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable P : PESKA.sink_policyA.

Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Abbreviation crun_pre := (PECA.crun_preA segs A AA E L ar P).
Abbreviation enc_at := (PECA.enc_atA segs E L ar).
Abbreviation sink_at := (PESKA.sink_atA segs L ar P).
Abbreviation parser_at := (PM.parser_at segs A accA annA).
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation content_ok := (PEC.content_ok segs A).
Abbreviation cfg := (PMSPA.cfg segs).
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation ffroomA := PMSPA.ffroomA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation frame_ok5 := PECA.frame_ok5.
Abbreviation o_p := (PMSPA.o_p A).
Abbreviation o_v := (PMSPA.o_v A).
Abbreviation o_is := (PMSPA.o_is A).
Abbreviation o_ec := (PMSPA.o_ec A).
Abbreviation o_src := (PMSPA.o_src A).
Abbreviation o_tb := (PMSPA.o_tb A).
Abbreviation o_sink := (PESK.o_sink E).
Abbreviation pot_all := (PECA.pot_allA L ar P).
Abbreviation pot_enc := (PECA.pot_encA L ar P).
Abbreviation W_crun := (PEC.W_crun A E).
Abbreviation W_enc := (PEC.W_enc A E).

Definition payload_ok (p : list Z) : Prop := bytes_ok p /\ blen p < 2 ^ 26.

Definition make_ec_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o v sp r : Z) (b : bool),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 v -> 1 <= v <= 64 ->
    aobjA FF o 16 -> o mod 8 = 0 -> L5.defined M o 16 -> accA M o 16 ->
    PMSTA.base_okA segs A M -> PESTA.err_okA segs A AA E M b ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> PMSPA.ec_at segs M' o v (pa_errcat_obj A) -> PESTA.err_okA segs A AA E M' true ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 1) ((o, 16) :: (if b then [] else PMSPA.err_W A)) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_make_ec A) M model) K.

Definition crun_spec (T : Type) (pc h : Z)
           (args : T -> bvmap 5 word -> Z -> Prop)
           (MP : T -> list Z -> st -> Prop)
           (F : T -> list Z -> st -> st) : Prop :=
  PESKA.spa_mode P ->
  forall (a : T) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomA h FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    args a R fb ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> MP a p X -> s_bad (F a p X) = false -> PESKA.spa_hb P (s_hi (F a p X)) ->
    PMSP.credit_le (pot_all s en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (F a p X) s' str sm' en' k' e' cat ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr h) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all s en k) (pot_all s' en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition args3 (_ : unit) (R : bvmap 5 word) (fb : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb).
Definition args_rv (t : Z) (R : bvmap 5 word) (fb : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_v fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ 0 <= t < 256 /\ getr R 12%bv = Z_to_bv 64 t.

Definition mp_run (_ : unit) (p : list Z) (X : st) : Prop :=
  pre_run p X /\ s_done X = false /\ s_halt X = false /\ 0 <= s_depth X <= UbjRef.MAX_DEPTH
  /\ Z.of_nat (length (s_estk X)) <= UbjRef.MAX_DEPTH /\ Z.of_nat (length (s_stk X)) <= s_depth X + 1.
Definition mp_rv (t : Z) (p : list Z) (X : st) : Prop :=
  pre_run p X /\ s_done X = false /\ s_halt X = false /\ 0 <= s_depth X <= UbjRef.MAX_DEPTH
  /\ Z.of_nat (length (s_estk X)) <= UbjRef.MAX_DEPTH /\ Z.of_nat (length (s_stk X)) <= s_depth X + 1.
Definition mp_end (_ : unit) (p : list Z) (X : st) : Prop :=
  pre p X /\ s_more X = true /\ s_done X = false /\ s_halt X = false /\ rinv X
  /\ exists t r, s_stk X = t :: r /\ container_mode (ps_mode t) = true /\ r <> [] /\ s_estk X <> [].

Definition rtv_spec : Prop := crun_spec unit (pa_rtv A) 9 args3 mp_run (fun _ p X => r_tv p X).
Definition read_value_spec : Prop := crun_spec Z (pa_read_value A) 8 args_rv mp_rv (fun t p X => r_value p t X).
Definition read_key_spec : Prop := crun_spec unit (pa_read_key A) 7 args3 mp_run (fun _ p X => r_key p X).
Definition begin_array_spec : Prop := crun_spec unit (pa_begin_array A) 7 args3 mp_run (fun _ p X => r_begin p false X).
Definition begin_object_spec : Prop := crun_spec unit (pa_begin_object A) 7 args3 mp_run (fun _ p X => r_begin p true X).

Definition end_array_spec : Prop := crun_spec unit (pa_end_array A) 5 args3 mp_end (fun _ p X => r_end X).
Definition end_object_spec : Prop := crun_spec unit (pa_end_object A) 5 args3 mp_end (fun _ p X => r_end X).

Definition args_gl (_ : unit) (R : bvmap 5 word) (fb : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_ec fb).
Definition mp_gl (_ : unit) (p : list Z) (X : st) : Prop :=
  bytes_ok p /\ 0 <= s_pos X <= blen p /\ s_more X = true /\ s_done X = false /\ s_halt X = false /\ s_bad X = false.
Definition gl_post (p : list Z) (X : st) : st :=
  match UbjRef.get_length p (s_pos X) with
  | Some (_, pos1) => w_pos pos1 X
  | None => r_fail X
  end.
Definition gl_ret (p : list Z) (X : st) (R' : bvmap 5 word) : Prop :=
  match UbjRef.get_length p (s_pos X) with
  | Some (n, _) => getr R' 10%bv = Z_to_bv 64 n
  | None => True
  end.
Definition get_length_spec : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 5 -> ffroomA 5 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    args_gl tt R fb ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> mp_gl tt p X ->
    PMSP.credit_le (pot_all s en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (gl_post p X) s' str sm' en k e' cat -> gl_ret p X R' ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        PM.p_tb s' = PM.p_tb s -> PM.p_tg s' = PM.p_tg s -> PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 5) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all s en k) (pot_all s' en k) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en k ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_get_length A) M model) K.

Definition parse_spec : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 10 -> ffroomA 10 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    args3 tt R fb ->
    crun_pre M fb p UbjRef.init s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> (forall n, PESKA.spa_hb P (s_hi (run n p UbjRef.init))) ->
    PMSP.credit_le (pot_all s en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (n : nat)
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        halted (run n p UbjRef.init) = true ->
        parser_at M' (o_p fb) (o_is fb) s' /\ iss_at M' (o_is fb) str sm' /\ enc_at M' (o_v fb) fb en' /\ sink_at M' (o_sink fb) k'
        /\ PMSTA.base_okA segs A M' /\ PESTA.err_okA segs A AA E M' e' /\ L5.defined M' (o_ec fb) 16
        /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 10) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all s en k) (PESKA.spa_pot P (PESK.sk_c k')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_parse A) M model) K.

Definition reader_read_spec : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 11 -> ffroomA 11 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_ec fb) ->
    parser_at M (o_p fb) (o_is fb) s /\ iss_at M (o_is fb) str sm /\ enc_at M (o_v fb) fb en /\ L5.u64_at segs M (o_p fb + 384) (o_v fb)
    /\ sink_at M (o_sink fb) k /\ PMSTA.base_okA segs A M /\ PESTA.err_okA segs A AA E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
    /\ content_ok M fb p (PM.p_src s) str sm /\ PMSPA.ec_at segs M (o_ec fb) 0 cat ->
    (1 <= length (PM.p_stk s))%nat -> PEC.pos_of p (PM.p_src s) sm = 0 ->
    PM.sr_rem (PM.p_src s) = 0 ->
    PEC.en_stk en = [] -> PEC.en_depth en = 0 -> PESK.sk_z k = 0 ->
    incl (PM.vs_own str) LBX ->
    payload_ok p -> (forall n, PESKA.spa_hb P (s_hi (run n p UbjRef.init))) ->
    PMSP.credit_le (pot_all (PMSPA.pst_reset s) en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (n : nat)
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        halted (run n p UbjRef.init) = true ->
        parser_at M' (o_p fb) (o_is fb) s' /\ iss_at M' (o_is fb) str sm' /\ enc_at M' (o_v fb) fb en' /\ sink_at M' (o_sink fb) k'
        /\ PMSTA.base_okA segs A M' /\ PESTA.err_okA segs A AA E M' e' /\ L5.defined M' (o_ec fb) 16
        /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 11) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all (PMSPA.pst_reset s) en k) (PESKA.spa_pot P (PESK.sk_c k')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reader_read A) M model) K.

Definition eslot_spec (T : Type) (pc : Z)
           (args : T -> list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
           (MP : T -> list Z -> st -> Prop)
           (F : T -> list Z -> st -> st) : Prop :=
  PESKA.spa_mode P ->
  forall (a : T) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 4 -> ffroomA 4 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_v fb) -> args a FF R M sp fb s ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> MP a p X -> s_bad (F a p X) = false -> PESKA.spa_hb P (s_hi (F a p X)) ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (F a p X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (W_enc fb) M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition mp_enc (p : list Z) (X : st) : Prop := s_lo X <= s_hi X /\ s_bad X = false /\ Forall ei_ok (s_estk X) /\ 0 <= s_edepth X <= UbjRef.MAX_DEPTH.

Definition mp_encb (p : list Z) (X : st) : Prop := mp_enc p X /\ Z.of_nat (length (s_estk X)) <= UbjRef.MAX_DEPTH.

Definition args_t3 (_ : unit) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := getr R 13%bv = Z_to_bv 64 (o_ec fb).
Definition v_null_spec : Prop := eslot_spec unit (pe_null E) args_t3 (fun _ => mp_enc) (fun _ _ X => e_scalar 1 1 X).

Definition args_bool (v : bool) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  getr R 11%bv = Z_to_bv 64 (PEC.b2z v) /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_bool_spec : Prop := eslot_spec bool (pe_bool E) args_bool (fun _ => mp_enc) (fun _ _ X => e_scalar 1 1 X).

Definition uint64_width (v : Z) : Z :=
  if v <=? 255 then 2 else if v <=? 32767 then 3 else if v <=? 2147483647 then 5 else 9.
Definition args_u64 (v : Z) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  0 <= v <= UbjRef.INT64_MAX /\ getr R 11%bv = Z_to_bv 64 v /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_uint64_spec : Prop :=
  eslot_spec Z (pe_uint64 E) args_u64 (fun _ => mp_enc) (fun v _ X => e_scalar (uint64_width v) (uint64_width v) X).

Definition int64_width (v : Z) : Z :=
  if 0 <=? v then uint64_width v
  else if -128 <=? v then 2 else if -32768 <=? v then 3 else if -2147483648 <=? v then 5 else 9.
Definition args_i64 (v : Z) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  - 2 ^ 63 <= v < 2 ^ 63 /\ getr R 11%bv = Z_to_bv 64 v /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_int64_spec : Prop :=
  eslot_spec Z (pe_int64 E) args_i64 (fun _ => mp_enc) (fun v _ X => e_scalar (int64_width v) (int64_width v) X).

Definition v_double_spec : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 4 -> ffroomA 4 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_v fb) -> getr R 13%bv = Z_to_bv 64 (o_ec fb) ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> mp_enc p X -> PESKA.spa_hb P (s_hi X + 9) ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit) (w : Z),
        regs_preserved R R' -> (w = 5 \/ w = 9) ->
        crun_pre M' fb p (e_scalar w w X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (W_enc fb) M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_double E) M model) K.

Definition v_begin_arr_spec : Prop := eslot_spec unit (pe_begin_arr E) args_t3 (fun _ => mp_encb) (fun _ _ X => e_begin_indef 3 X).
Definition v_begin_obj_spec : Prop := eslot_spec unit (pe_begin_obj E) args_t3 (fun _ => mp_encb) (fun _ _ X => e_begin_indef 1 X).

Definition args_len (n : Z) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  0 <= n <= UbjRef.MAX_ITEMS /\ getr R 11%bv = Z_to_bv 64 n /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_begin_arr_len_spec : Prop := eslot_spec Z (pe_begin_arr_len E) args_len (fun _ => mp_encb) (fun n _ X => e_begin_len 2 n X).
Definition v_begin_obj_len_spec : Prop := eslot_spec Z (pe_begin_obj_len E) args_len (fun _ => mp_encb) (fun n _ X => e_begin_len 0 n X).

Definition args_t2 (_ : unit) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := getr R 12%bv = Z_to_bv 64 (o_ec fb).
Definition mp_ence (p : list Z) (X : st) : Prop := mp_enc p X /\ 1 <= s_edepth X.
Definition v_end_arr_spec : Prop := eslot_spec unit (pe_end_arr E) args_t2 (fun _ => mp_ence) (fun _ _ X => e_end X).
Definition v_end_obj_spec : Prop := eslot_spec unit (pe_end_obj E) args_t2 (fun _ => mp_ence) (fun _ _ X => e_end X).

Definition args_sv (d : Z * list Z) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists sv, getr R 11%bv = Z_to_bv 64 sv /\ sv mod 8 = 0 /\ aobjA FF sv 16 /\ accA M sv 16 /\ (sv + 16 <= fb \/ fb + 2048 <= sv)
  /\ L5.u64_at segs M sv (fst d) /\ L5.u64_at segs M (sv + 8) (Z.of_nat (length (snd d)))
  /\ L5.bytes_at segs M (fst d) (snd d) /\ bytes_ok (snd d) /\ Z.of_nat (length (snd d)) < 2 ^ 26
  /\ L5.defined M (fst d) (Z.of_nat (length (snd d))) /\ accA M (fst d) (Z.of_nat (length (snd d)))
  /\ (   (exists B m, In (B, m) (PM.parser_own s) /\ B <= fst d /\ fst d + Z.of_nat (length (snd d)) <= B + m)
      \/ (o_tb fb + 1 <= fst d /\ fst d + Z.of_nat (length (snd d)) <= o_tb fb + 24)
      \/ (fst d = 0 /\ snd d = [])
      \/ (aobjA FF (fst d) (Z.of_nat (length (snd d))) /\ (fst d + Z.of_nat (length (snd d)) <= fb \/ fb + 2048 <= fst d))).
Definition args_key (d : Z * list Z) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  args_sv d FF R M sp fb s /\ getr R 13%bv = Z_to_bv 64 (o_ec fb) /\ UbjRef.utf8_valid (snd d) = true.
Definition v_key_spec : Prop :=
  eslot_spec (Z * list Z) (pe_key E) args_key (fun _ => mp_enc) (fun d _ X => e_key (Z.of_nat (length (snd d))) X).

Definition args_str (d : Z * list Z) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  args_sv d FF R M sp fb s /\ getr R 14%bv = Z_to_bv 64 (o_ec fb) /\ (exists tg, 0 <= tg < 32 /\ getr R 12%bv = Z_to_bv 64 tg).
Definition v_string_spec : Prop :=
  eslot_spec (Z * list Z) (pe_string E) args_str (fun _ => mp_enc)
             (fun d _ X => e_string (UbjRef.utf8_valid (snd d)) (Z.of_nat (length (snd d))) X).

Definition v_flush_spec : Prop := eslot_spec unit (pe_flush E) (fun _ _ _ _ _ _ _ => True) (fun _ _ _ => True) (fun _ _ X => X).

Definition put_length_spec : Prop :=
  PESKA.spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 3 -> ffroomA 3 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 16 = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_v fb) -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n <= UbjRef.INT64_MAX ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> mp_enc p X -> PESKA.spa_hb P (s_hi X + pl_size n) ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (k' : PESK.sink) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (w_out (pl_size n) (pl_size n) X) s str sm en k' e cat ->
        L5CA.ahpres L ar (PM.parser_own s ++ PEC.enc_own en ++ LBX) FF sp (PMSPA.pm_scr 3) [(o_sink fb, 24)] M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s en k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_put_length E) M model) K.

Definition evec_alloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (n sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 11%bv = Z_to_bv 64 n -> 1 <= n <= 4096 -> PMSTA.base_okA segs A M ->
    PMSP.credit_le (scA (PM.cost1 HV (PEC.ESZ * n))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit) (B : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 B -> getr R' 11%bv = Z_to_bv 64 n ->
        L5CA.afresh L ar LB (FF ++ LK) M' B (PEC.ESZ * n) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 1) [] M M' ->
        PMSP.credit_keep cr cr' (scA (PM.cost1 HV (PEC.ESZ * n))) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI ((B, PEC.ESZ * n) :: LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_evec_alloc E) M model) K.

Definition evec_sbdtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (q f b c sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 q -> aobjA FF q 32 -> q mod 8 = 0 -> L5.defined M q 32 -> accA M q 32 ->
    L5.u64_at segs M q f -> L5.u64_at segs M (q + 8) b -> L5.u64_at segs M (q + 16) b -> L5.u64_at segs M (q + 24) (f + c) ->
    (f = 0 \/ In (f, c) LB) -> PMSTA.base_okA segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit),
        regs_preserved R R' ->
        L5CA.ahpres L ar (if f =? 0 then LB else lb_remove f LB) FF sp (PMSPA.pm_scr 1) [(q, 32)] M M' ->
        PMSP.credit_le cr cr' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (if f =? 0 then LB else lb_remove f LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_evec_sbdtor E) M model) K.

Definition cwin (M : word -> option byte) (p : list Z) (src : PM.srcst) (sm : PM.strm) : Prop :=
  0 <= PEC.pos_of p src sm <= blen p /\ L5.bytes_at segs M (PM.sr_de src) (UbjRef.slice p (PEC.pos_of p src sm) (PM.sr_rem src))
  /\ (PM.sm_st sm = 2 -> PM.sm_g sm = PM.sm_eg sm).

Definition csrc_spec (pc h aln : Z) (args : list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
           (Wx : bvmap 5 word -> list L5.range -> Prop)
           (res : list Z -> bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomA h FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod aln = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> args FF R M sp fb s -> Wx R Wextra ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> accA M (o_p fb) PECA.RDR_BYTES ->
    incl (PM.vs_own str) LBX ->
    payload_ok p -> content_ok M fb p (PM.p_src s) str sm ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        parser_at M' (o_p fb) (o_is fb) (PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) src' (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s)) ->
        iss_at M' (o_is fb) str sm' -> PMSPA.src_step (PM.p_src s) src' sm sm' ->
        res p R R' M' (PM.p_src s) src' sm sm' ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr h) (PMSPA.W_src A fb (PM.p_src s) ++ Wextra) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition cpeek_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  PMSPA.consumed src src' sm sm' = 0 /\ cwin M' p src' sm' /\
  (   (getr R' 10%bv = Z_to_bv 64 256 /\ PEC.pos_of p src' sm' = blen p)
   \/ (PEC.pos_of p src' sm' < blen p /\ getr R' 10%bv = Z_to_bv 64 (bat p (PEC.pos_of p src' sm')) /\ 1 <= PM.sr_rem src')).
Definition peek_spec : Prop := csrc_spec (pa_peek A) 4 32 PMSPA.no_args PMSPA.no_W cpeek_res.

Definition cignore_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  cwin M' p src' sm' /\
  ((PMSPA.consumed src src' sm sm' = 1) \/ (PMSPA.consumed src src' sm sm' = 0 /\ PM.unread src' sm' = 0)).
Definition ignore_spec : Prop := csrc_spec (pa_ignore A) 4 32 PMSPA.ignore_args PMSPA.no_W cignore_res.

Definition cread_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  cwin M' p src' sm' /\
  exists q kk d, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 kk /\ 4096 <= q /\ q + kk <= 2 ^ 47 /\ 1 <= kk <= PM.CHUNK
    /\ getr R' 10%bv = Z_to_bv 64 d /\ 0 <= d <= kk
    /\ PMSPA.consumed src src' sm sm' = d /\ (d < kk -> PM.unread src' sm' = 0)
    /\ L5.defined M' q d /\ L5.bytes_at segs M' q (UbjRef.slice p (PEC.pos_of p src sm) d).

Definition cread_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists q kk, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 kk /\ 1 <= kk <= 8
    /\ aobjA FF q kk /\ L5.defined M q kk /\ accA M q kk
    /\ (q + kk <= o_is fb \/ o_is fb + 272 <= q) /\ (q + kk <= o_p fb \/ o_p fb + PECA.RDR_BYTES <= q).

Definition cread_W (R : bvmap 5 word) (W : list L5.range) : Prop :=
  exists q kk, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 kk /\ 0 <= q < 2 ^ 64 /\ 0 <= kk < 2 ^ 64 /\ W = [(q, kk)].
Definition src_read_spec (aln : Z) : Prop := csrc_spec (pa_src_read A) 4 aln cread_args cread_W cread_res.

Definition cfill_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  src' = src /\ exists c, getr R' 10%bv = Z_to_bv 64 c /\ 0 <= c <= PM.CHUNK /\ PM.sm_g sm' = PM.sm_g sm + c
    /\ (c < PM.CHUNK -> PM.sm_g sm' = PM.sm_eg sm /\ PM.sm_st sm' = 2) /\ (PM.sm_st sm = 2 -> c = 0)
    /\ L5.bytes_at segs M' (PM.sr_qc src) (UbjRef.slice p (blen p - (PM.sm_eg sm - PM.sm_g sm)) c)
    /\ (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm').
Definition fill_args (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  getr R 12%bv = Z_to_bv 64 PM.CHUNK
  /\ exists os q, getr R 10%bv = Z_to_bv 64 os /\ 0 <= os < 2 ^ 64 /\ getr R 11%bv = Z_to_bv 64 q /\ 0 <= q < 2 ^ 64 /\ L5.u64_at segs M (os + 264) q.

Definition fill_buffer_spec : Prop := csrc_spec (pa_fill_buffer A) 3 16 fill_args PMSPA.no_W cfill_res.

Definition read_span_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb len : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomA 6 FF LK -> ffrsA FF sp -> frame_ok5 FF fb -> sp mod 32 = 0 ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (o_tb fb) -> 0 <= len < 2 ^ 64 ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> accA M (o_p fb) PECA.RDR_BYTES -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> payload_ok p -> content_ok M fb p (PM.p_src s) str sm ->
    PMSP.credit_le (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (o_tb fb + 1 <= ptr /\ ptr + n <= o_tb fb + 24)) ->
        L5.defined M' ptr n -> accA M' ptr n -> L5.bytes_at segs M' ptr (UbjRef.slice p (PEC.pos_of p (PM.p_src s) sm) n) ->
        n = Z.min len (blen p - PEC.pos_of p (PM.p_src s) sm) ->
        parser_at M' (o_p fb) (o_is fb) s' -> iss_at M' (o_is fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        content_ok M' fb p (PM.p_src s') str sm' ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> PMSPA.consumed (PM.p_src s) (PM.p_src s') sm sm' = n ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 6) (PMSPA.W_srcf A fb ++ [(o_tb fb, 24)]) M M' ->
        PMSP.credit_keep cr cr' (scA (PM.pot_text HV (PM.p_tb s) (PM.p_tg s))) (scA (PM.pot_text HV (PM.p_tb s') (PM.p_tg s'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_read_span A) M model) K.

Definition str_ctor_c_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o ptr n sp r : Z) (l : list Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ptr -> getr R 12%bv = Z_to_bv 64 n ->
    0 <= n < 2 ^ 26 -> aobjA FF o 24 -> o mod 8 = 0 -> L5.defined M o 24 -> accA M o 24 ->
    (n = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + n <= B + m)) -> aacc M ptr n ->
    Z.of_nat (length l) = n -> L5.bytes_at segs M ptr l ->
    PMSP.credit_le (scA (PM.cost1 HV (n + 16))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s : PM.vstr) (cr' : credit),
        regs_preserved R R' -> PM.vstr_at segs accA M' o s -> PM.vs_size s = n ->
        (n <= 22 -> s = PM.VShort n) -> (23 <= n -> exists q, s = PM.VLong (PMSPA.str_count n) n q) ->
        L5.bytes_at segs M' (PM.vs_data o s) l ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 0) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (scA (PM.cost1 HV (n + 16))) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_str_ctor A) M model) K.

Definition iss_ctor_c_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (ois os sp r : Z) (s : PM.vstr) (b : bool) (l : list Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 4 -> ffroomA 4 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 ois -> getr R 11%bv = Z_to_bv 64 os -> getr R 12%bv = Z_to_bv 64 8 ->
    aobjA FF ois 272 -> aobjA FF os 24 -> ois = os + 64 -> ois mod 8 = 0 -> os mod 8 = 0 -> L5.defined M ois 272 -> accA M ois 272 ->
    PM.vstr_at segs accA M os s -> incl (PM.vs_own s) LB -> PM.vs_size s < 2 ^ 26 -> (forall c n q, s = PM.VLong c n q -> 23 <= n) ->
    Z.of_nat (length l) = PM.vs_size s -> L5.bytes_at segs M (PM.vs_data os s) l ->
    PMSTA.base_okA segs A M -> PMST.loc_ok segs A M b ->
    PMSP.credit_le (scA (PM.cost1 HV (PM.vs_size s + 32))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.vstr) (sm : PM.strm) (cr' : credit),
        regs_preserved R R' -> iss_at M' ois s' sm -> PM.vs_size s' = PM.vs_size s ->
        PM.sm_g sm = PM.vs_data (ois + 80) s' -> PM.sm_st sm = 0 ->
        L5.bytes_at segs M' (PM.vs_data (ois + 80) s') l ->
        PMST.loc_ok segs A M' true ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 4) ((ois, 272) :: (if b then [] else PMSPA.loc_W A)) M M' ->
        PMSP.credit_keep cr cr' (scA (PM.cost1 HV (PM.vs_size s + 32))) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_iss_ctor A) M model) K.

Definition pay_in (PayOk : list byte -> Prop) : Prop :=
  forall payload, Z.of_nat (length payload) < 2 ^ 26 -> PayOk payload ->
  forall n, PESKA.spa_hb P (s_hi (run n (map bv_unsigned payload) UbjRef.init)).
Definition pay_out (PayExport : list byte -> Prop) : Prop :=
  forall payload c, Z.of_nat (length payload) < 2 ^ 26 -> PESK.is_cap c -> (0 < c -> PESKA.spa_cap P c) ->
  0 <= UbjRefFactsS9.F (map bv_unsigned payload) <= c -> PayExport payload.

Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PM.pst),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp -> frame_ok5 FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> parser_at M (o_p fb) (o_is fb) s -> (1 <= length (PM.p_stk s))%nat ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> parser_at M' (o_p fb) (o_is fb) (PMSPA.pst_reset s) ->

        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 1) [(o_p fb + 8, 8); (o_tb fb, 24); (PMSPA.o_vec A fb, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reset A) M model) K.

Definition reader_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb oo oa : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomA 6 FF LK -> ffrsA FF sp -> frame_ok5 FF fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_is fb) -> getr R 12%bv = Z_to_bv 64 oo -> getr R 13%bv = Z_to_bv 64 oa ->
    oo = o_p fb + 464 -> L5.defined M (o_p fb) 384 -> accA M (o_p fb) 384 -> accA M oo 32 -> L5.u64_at segs M oo (pa_vp_opts A) -> L5.u64_at segs M (oo + 8) PM.MAX_ITEMS -> L5.u32_at segs M (oo + 24) PM.MAX_DEPTH ->
    iss_at M (o_is fb) str sm -> PMSTA.base_okA segs A M -> (PMST.loc_ok segs A) M true ->
    PMSP.credit_le (scA (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (qc b : Z) (cr' : credit),
        regs_preserved R R' -> parser_at M' (o_p fb) (o_is fb) (PMSPA.parser_init qc b) ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 6) [(o_p fb, 384)] M M' ->
        PMSP.credit_keep cr cr' (scA (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) PMSP.cr0 ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own (PMSPA.parser_init qc b) ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reader_ctor A) M model) K.

End Specs.
End PECSPA.
