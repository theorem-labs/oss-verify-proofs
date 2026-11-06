(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCStatics PeCModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : pe_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation crun_pre := (PEC.crun_pre segs A E L T3 T4 P).
Abbreviation enc_at := (PEC.enc_at segs E L T3 T4).
Abbreviation sink_at := (PESK.sink_at segs L T3 T4 P).
Abbreviation parser_at := (PM.parser_at segs A T3 T4).
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation content_ok := (PEC.content_ok segs A).
Abbreviation cfg := (PMSP.cfg segs).
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation o_p := (PMSP.o_p A).
Abbreviation o_v := (PMSP.o_v A).
Abbreviation o_is := (PMSP.o_is A).
Abbreviation o_ec := (PMSP.o_ec A).
Abbreviation o_src := (PMSP.o_src A).
Abbreviation o_tb := (PMSP.o_tb A).
Abbreviation o_sink := (PESK.o_sink E).
Abbreviation pot_all := (PEC.pot_all L P).
Abbreviation pot_enc := (PEC.pot_enc L P).
Abbreviation W_crun := (PEC.W_crun A E).
Abbreviation W_enc := (PEC.W_enc A E).

Definition payload_ok (p : list Z) : Prop := bytes_ok p /\ blen p < 2 ^ 26.

Definition make_ec_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o v sp r : Z) (b : bool),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 v -> 1 <= v <= 64 ->
    sp <= o -> o + 16 <= hl_sptop L -> o mod 8 = 0 -> L5.defined M o 16 ->
    PMST.base_ok segs A M -> PEST.err_ok segs A E M b ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> PMSP.ec_at segs M' o v (pa_errcat_obj A) -> PEST.err_ok segs A E M' true ->
        L5C.hpres L LB sp (PMSP.pm_scr 1) ((o, 16) :: (if b then [] else PMSP.err_W A)) M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (cfg R' r M' model) K) ->
    srealizes segs SCFG (cfg R (pa_make_ec A) M model) K.

Definition crun_spec (T : Type) (pc h : Z)
           (args : T -> bvmap 5 word -> Z -> Prop)
           (MP : T -> list Z -> st -> Prop)
           (F : T -> list Z -> st -> st) : Prop :=
  PESK.sp_mode P ->
  forall (a : T) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    args a R fb ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> MP a p X -> s_bad (F a p X) = false -> PESK.sp_hb P (s_hi (F a p X)) ->
    PMSP.credit_le (pot_all s en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (F a p X) s' str sm' en' k' e' cat ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5C.hpres L LBX sp (PMSP.pm_scr h) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all s en k) (pot_all s' en' k') ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s' en' k' ++ LBX) cr' M' (m_vmmaps model') ->
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
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 5 -> frame_ok sp fb ->
    args_gl tt R fb ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> mp_gl tt p X ->
    PMSP.credit_le (pot_all s en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
            (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (gl_post p X) s' str sm' en k e' cat -> gl_ret p X R' ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        PM.p_tb s' = PM.p_tb s -> PM.p_tg s' = PM.p_tg s -> PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s ->
        L5C.hpres L LBX sp (PMSP.pm_scr 5) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all s en k) (pot_all s' en k) ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s' en k ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_get_length A) M model) K.

Definition parse_spec : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 10 -> frame_ok sp fb ->
    args3 tt R fb ->
    crun_pre M fb p UbjRef.init s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> (forall n, PESK.sp_hb P (s_hi (run n p UbjRef.init))) ->
    PMSP.credit_le (pot_all s en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (n : nat)
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        halted (run n p UbjRef.init) = true ->
        parser_at M' (o_p fb) (o_is fb) s' /\ iss_at M' (o_is fb) str sm' /\ enc_at M' (o_v fb) fb en' /\ sink_at M' (o_sink fb) k'
        /\ PMST.base_ok segs A M' /\ PEST.err_ok segs A E M' e' /\ L5.defined M' (o_ec fb) 16
        /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5C.hpres L LBX sp (PMSP.pm_scr 10) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all s en k) (PESK.sink_pot P (PESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s' en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_parse A) M model) K.

Definition reader_read_spec : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 11 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_ec fb) ->
    parser_at M (o_p fb) (o_is fb) s /\ iss_at M (o_is fb) str sm /\ enc_at M (o_v fb) fb en /\ L5.u64_at segs M (o_p fb + 384) (o_v fb)
    /\ sink_at M (o_sink fb) k /\ PMST.base_ok segs A M /\ PEST.err_ok segs A E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
    /\ content_ok M fb p (PM.p_src s) str sm /\ PMSP.ec_at segs M (o_ec fb) 0 cat ->
    (1 <= length (PM.p_stk s))%nat -> PEC.pos_of p (PM.p_src s) sm = 0 ->
    PM.sr_rem (PM.p_src s) = 0 ->
    PEC.en_stk en = [] -> PEC.en_depth en = 0 -> PESK.sk_z k = 0 ->
    incl (PM.vs_own str) LBX ->
    payload_ok p -> (forall n, PESK.sp_hb P (s_hi (run n p UbjRef.init))) ->
    PMSP.credit_le (pot_all (PMSP.pst_reset s) en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (n : nat)
            (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        halted (run n p UbjRef.init) = true ->
        parser_at M' (o_p fb) (o_is fb) s' /\ iss_at M' (o_is fb) str sm' /\ enc_at M' (o_v fb) fb en' /\ sink_at M' (o_sink fb) k'
        /\ PMST.base_ok segs A M' /\ PEST.err_ok segs A E M' e' /\ L5.defined M' (o_ec fb) 16
        /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        L5C.hpres L LBX sp (PMSP.pm_scr 11) (W_crun fb) M M' ->
        PMSP.credit_keep cr cr' (pot_all (PMSP.pst_reset s) en k) (PESK.sink_pot P (PESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s' en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_reader_read A) M model) K.

Definition eslot_spec (T : Type) (pc : Z)
           (args : T -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
           (MP : T -> list Z -> st -> Prop)
           (F : T -> list Z -> st -> st) : Prop :=
  PESK.sp_mode P ->
  forall (a : T) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 4 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_v fb) -> args a R M sp fb s ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> MP a p X -> s_bad (F a p X) = false -> PESK.sp_hb P (s_hi (F a p X)) ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (F a p X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5C.hpres L (PM.parser_own s ++ LBX) sp (PMSP.pm_scr 4) (W_enc fb) M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en' k') ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition mp_enc (p : list Z) (X : st) : Prop := s_lo X <= s_hi X /\ s_bad X = false /\ Forall ei_ok (s_estk X) /\ 0 <= s_edepth X <= UbjRef.MAX_DEPTH.

Definition mp_encb (p : list Z) (X : st) : Prop := mp_enc p X /\ Z.of_nat (length (s_estk X)) <= UbjRef.MAX_DEPTH.

Definition args_t3 (_ : unit) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := getr R 13%bv = Z_to_bv 64 (o_ec fb).
Definition v_null_spec : Prop := eslot_spec unit (pe_null E) args_t3 (fun _ => mp_enc) (fun _ _ X => e_scalar 1 1 X).

Definition args_bool (v : bool) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  getr R 11%bv = Z_to_bv 64 (PEC.b2z v) /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_bool_spec : Prop := eslot_spec bool (pe_bool E) args_bool (fun _ => mp_enc) (fun _ _ X => e_scalar 1 1 X).

Definition uint64_width (v : Z) : Z :=
  if v <=? 255 then 2 else if v <=? 32767 then 3 else if v <=? 2147483647 then 5 else 9.
Definition args_u64 (v : Z) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  0 <= v <= UbjRef.INT64_MAX /\ getr R 11%bv = Z_to_bv 64 v /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_uint64_spec : Prop :=
  eslot_spec Z (pe_uint64 E) args_u64 (fun _ => mp_enc) (fun v _ X => e_scalar (uint64_width v) (uint64_width v) X).

Definition int64_width (v : Z) : Z :=
  if 0 <=? v then uint64_width v
  else if -128 <=? v then 2 else if -32768 <=? v then 3 else if -2147483648 <=? v then 5 else 9.
Definition args_i64 (v : Z) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  - 2 ^ 63 <= v < 2 ^ 63 /\ getr R 11%bv = Z_to_bv 64 v /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_int64_spec : Prop :=
  eslot_spec Z (pe_int64 E) args_i64 (fun _ => mp_enc) (fun v _ X => e_scalar (int64_width v) (int64_width v) X).

Definition v_double_spec : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 4 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_v fb) -> getr R 13%bv = Z_to_bv 64 (o_ec fb) ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> mp_enc p X -> PESK.sp_hb P (s_hi X + 9) ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit) (w : Z),
        regs_preserved R R' -> (w = 5 \/ w = 9) ->
        crun_pre M' fb p (e_scalar w w X) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5C.hpres L (PM.parser_own s ++ LBX) sp (PMSP.pm_scr 4) (W_enc fb) M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en' k') ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_double E) M model) K.

Definition v_begin_arr_spec : Prop := eslot_spec unit (pe_begin_arr E) args_t3 (fun _ => mp_encb) (fun _ _ X => e_begin_indef 3 X).
Definition v_begin_obj_spec : Prop := eslot_spec unit (pe_begin_obj E) args_t3 (fun _ => mp_encb) (fun _ _ X => e_begin_indef 1 X).

Definition args_len (n : Z) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  0 <= n <= UbjRef.MAX_ITEMS /\ getr R 11%bv = Z_to_bv 64 n /\ getr R 14%bv = Z_to_bv 64 (o_ec fb).
Definition v_begin_arr_len_spec : Prop := eslot_spec Z (pe_begin_arr_len E) args_len (fun _ => mp_encb) (fun n _ X => e_begin_len 2 n X).
Definition v_begin_obj_len_spec : Prop := eslot_spec Z (pe_begin_obj_len E) args_len (fun _ => mp_encb) (fun n _ X => e_begin_len 0 n X).

Definition args_t2 (_ : unit) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := getr R 12%bv = Z_to_bv 64 (o_ec fb).
Definition mp_ence (p : list Z) (X : st) : Prop := mp_enc p X /\ 1 <= s_edepth X.
Definition v_end_arr_spec : Prop := eslot_spec unit (pe_end_arr E) args_t2 (fun _ => mp_ence) (fun _ _ X => e_end X).
Definition v_end_obj_spec : Prop := eslot_spec unit (pe_end_obj E) args_t2 (fun _ => mp_ence) (fun _ _ X => e_end X).

Definition args_sv (d : Z * list Z) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists sv, getr R 11%bv = Z_to_bv 64 sv /\ sv mod 8 = 0 /\ sp <= sv /\ sv + 16 <= fb
  /\ L5.u64_at segs M sv (fst d) /\ L5.u64_at segs M (sv + 8) (Z.of_nat (length (snd d)))
  /\ L5.bytes_at segs M (fst d) (snd d) /\ bytes_ok (snd d) /\ Z.of_nat (length (snd d)) < 2 ^ 26
  /\ L5.defined M (fst d) (Z.of_nat (length (snd d)))
  /\ (   (exists B m, In (B, m) (PM.parser_own s) /\ B <= fst d /\ fst d + Z.of_nat (length (snd d)) <= B + m)
      \/ (sp <= fst d /\ fst d + Z.of_nat (length (snd d)) <= o_v fb)
      \/ (fst d = 0 /\ snd d = [])).
Definition args_key (d : Z * list Z) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  args_sv d R M sp fb s /\ getr R 13%bv = Z_to_bv 64 (o_ec fb) /\ UbjRef.utf8_valid (snd d) = true.
Definition v_key_spec : Prop :=
  eslot_spec (Z * list Z) (pe_key E) args_key (fun _ => mp_enc) (fun d _ X => e_key (Z.of_nat (length (snd d))) X).

Definition args_str (d : Z * list Z) (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  args_sv d R M sp fb s /\ getr R 14%bv = Z_to_bv 64 (o_ec fb) /\ (exists tg, 0 <= tg < 32 /\ getr R 12%bv = Z_to_bv 64 tg).
Definition v_string_spec : Prop :=
  eslot_spec (Z * list Z) (pe_string E) args_str (fun _ => mp_enc)
             (fun d _ X => e_string (UbjRef.utf8_valid (snd d)) (Z.of_nat (length (snd d))) X).

Definition v_flush_spec : Prop := eslot_spec unit (pe_flush E) (fun _ _ _ _ _ _ => True) (fun _ _ _ => True) (fun _ _ X => X).

Definition put_length_spec : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (p : list Z) (X : st)
         (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    hi_heap HI (PEC.owned s en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 3 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_v fb) -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n <= UbjRef.INT64_MAX ->
    crun_pre M fb p X s str sm en k e cat -> incl (PM.vs_own str) LBX ->
    payload_ok p -> mp_enc p X -> PESK.sp_hb P (s_hi X + pl_size n) ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (k' : PESK.sink) (cr' : credit),
        regs_preserved R R' ->
        crun_pre M' fb p (w_out (pl_size n) (pl_size n) X) s str sm en k' e cat ->
        L5C.hpres L (PM.parser_own s ++ PEC.enc_own en ++ LBX) sp (PMSP.pm_scr 3) [(o_sink fb, 24)] M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en k') ->
        model_but_vm model model' -> hi_heap HI (PEC.owned s en k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_put_length E) M model) K.

Definition evec_alloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 11%bv = Z_to_bv 64 n -> 1 <= n <= 4096 -> PMST.base_ok segs A M ->
    PMSP.credit_le (PM.cost1 L (PEC.ESZ * n)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit) (B : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 B -> getr R' 11%bv = Z_to_bv 64 n ->
        L5C.fresh_block L LB M' B (PEC.ESZ * n) ->
        L5C.hpres L LB sp (PMSP.pm_scr 1) [] M M' ->
        PMSP.credit_keep cr cr' (PM.cost1 L (PEC.ESZ * n)) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI ((B, PEC.ESZ * n) :: LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_evec_alloc E) M model) K.

Definition evec_sbdtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (q f b c sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 q -> sp <= q -> q + 32 <= hl_sptop L -> q mod 8 = 0 -> L5.defined M q 32 ->
    L5.u64_at segs M q f -> L5.u64_at segs M (q + 8) b -> L5.u64_at segs M (q + 16) b -> L5.u64_at segs M (q + 24) (f + c) ->
    (f = 0 \/ In (f, c) LB) -> PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        regs_preserved R R' ->
        L5C.hpres L (if f =? 0 then LB else lb_remove f LB) sp (PMSP.pm_scr 1) [(q, 32)] M M' ->
        PMSP.credit_le cr cr' ->
        model_but_vm model model' -> hi_heap HI (if f =? 0 then LB else lb_remove f LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pe_evec_sbdtor E) M model) K.

Definition cwin (M : word -> option byte) (p : list Z) (src : PM.srcst) (sm : PM.strm) : Prop :=
  0 <= PEC.pos_of p src sm <= blen p /\ L5.bytes_at segs M (PM.sr_de src) (UbjRef.slice p (PEC.pos_of p src sm) (PM.sr_rem src))
  /\ (PM.sm_st sm = 2 -> PM.sm_g sm = PM.sm_eg sm).

Definition csrc_spec (pc h : Z) (args : bvmap 5 word -> (word -> option byte) -> Z -> Prop)
           (Wx : bvmap 5 word -> list L5.range -> Prop)
           (res : list Z -> bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> args R M sp -> Wx R Wextra ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX ->
    payload_ok p -> content_ok M fb p (PM.p_src s) str sm ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        parser_at M' (o_p fb) (o_is fb) (PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) src' (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s)) ->
        iss_at M' (o_is fb) str sm' -> PMSP.src_step (PM.p_src s) src' sm sm' ->
        res p R R' M' (PM.p_src s) src' sm sm' ->
        L5C.hpres L (PM.parser_own s ++ LBX) sp (PMSP.pm_scr h) (PMSP.W_src A fb (PM.p_src s) ++ Wextra) M M' ->
        hi_heap HI (PM.parser_own s ++ LBX) cr M' (m_vmmaps model) ->
        srealizes segs SCFG (cfg R' r M' model) K) ->
    srealizes segs SCFG (cfg R pc M model) K.

Definition cpeek_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  PMSP.consumed src src' sm sm' = 0 /\ cwin M' p src' sm' /\
  (   (getr R' 10%bv = Z_to_bv 64 256 /\ PEC.pos_of p src' sm' = blen p)
   \/ (PEC.pos_of p src' sm' < blen p /\ getr R' 10%bv = Z_to_bv 64 (bat p (PEC.pos_of p src' sm')) /\ 1 <= PM.sr_rem src')).
Definition peek_spec : Prop := csrc_spec (pa_peek A) 4 PMSP.no_args PMSP.no_W cpeek_res.

Definition cignore_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  cwin M' p src' sm' /\
  ((PMSP.consumed src src' sm sm' = 1) \/ (PMSP.consumed src src' sm sm' = 0 /\ PM.unread src' sm' = 0)).
Definition ignore_spec : Prop := csrc_spec (pa_ignore A) 4 PMSP.ignore_args PMSP.no_W cignore_res.

Definition cread_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  cwin M' p src' sm' /\
  exists q kk d, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 kk /\ 4096 <= q /\ q + kk <= 2 ^ 47 /\ 1 <= kk <= PM.CHUNK
    /\ getr R' 10%bv = Z_to_bv 64 d /\ 0 <= d <= kk
    /\ PMSP.consumed src src' sm sm' = d /\ (d < kk -> PM.unread src' sm' = 0)
    /\ L5.defined M' q d /\ L5.bytes_at segs M' q (UbjRef.slice p (PEC.pos_of p src sm) d).

Definition cread_args (R : bvmap 5 word) (M : word -> option byte) (sp : Z) : Prop :=
  exists q kk, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 kk /\ 1 <= kk <= 8 /\ sp <= q
    /\ q + kk + pa_off_p A + 24 <= bv_unsigned (getr R 10%bv) /\ L5.defined M q kk.

Definition cread_W (R : bvmap 5 word) (W : list L5.range) : Prop :=
  exists q kk, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 kk /\ 0 <= q < 2 ^ 64 /\ 0 <= kk < 2 ^ 64 /\ W = [(q, kk)].
Definition src_read_spec : Prop := csrc_spec (pa_src_read A) 4 cread_args cread_W cread_res.

Definition cfill_res (p : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  src' = src /\ exists c, getr R' 10%bv = Z_to_bv 64 c /\ 0 <= c <= PM.CHUNK /\ PM.sm_g sm' = PM.sm_g sm + c
    /\ (c < PM.CHUNK -> PM.sm_g sm' = PM.sm_eg sm /\ PM.sm_st sm' = 2) /\ (PM.sm_st sm = 2 -> c = 0)
    /\ L5.bytes_at segs M' (PM.sr_qc src) (UbjRef.slice p (blen p - (PM.sm_eg sm - PM.sm_g sm)) c)
    /\ (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm').
Definition fill_args (R : bvmap 5 word) (M : word -> option byte) (sp : Z) : Prop :=
  getr R 12%bv = Z_to_bv 64 PM.CHUNK
  /\ exists os q, getr R 10%bv = Z_to_bv 64 os /\ 0 <= os < 2 ^ 64 /\ getr R 11%bv = Z_to_bv 64 q /\ 0 <= q < 2 ^ 64 /\ L5.u64_at segs M (os + 264) q.

Definition fill_buffer_spec : Prop := csrc_spec (pa_fill_buffer A) 3 fill_args PMSP.no_W cfill_res.

Definition read_span_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb len : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 6 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (o_tb fb) -> 0 <= len < 2 ^ 64 ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMST.base_ok segs A M -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> payload_ok p -> content_ok M fb p (PM.p_src s) str sm ->
    PMSP.credit_le (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (o_tb fb + 1 <= ptr /\ ptr + n <= o_tb fb + 24)) ->
        L5.defined M' ptr n -> L5.bytes_at segs M' ptr (UbjRef.slice p (PEC.pos_of p (PM.p_src s) sm) n) ->
        n = Z.min len (blen p - PEC.pos_of p (PM.p_src s) sm) ->
        parser_at M' (o_p fb) (o_is fb) s' -> iss_at M' (o_is fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        content_ok M' fb p (PM.p_src s') str sm' ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' -> PMSP.consumed (PM.p_src s) (PM.p_src s') sm sm' = n ->
        L5C.hpres L LBX sp (PMSP.pm_scr 6) (PMSP.W_srcf A fb ++ [(o_tb fb, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
        model_but_vm model model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_read_span A) M model) K.

Definition str_ctor_c_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o ptr n sp r : Z) (l : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ptr -> getr R 12%bv = Z_to_bv 64 n ->
    0 <= n < 2 ^ 26 -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 -> L5.defined M o 24 ->
    (n = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + n <= B + m)) ->
    Z.of_nat (length l) = n -> L5.bytes_at segs M ptr l ->
    PMSP.credit_le (PM.cost1 L (n + 16)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s : PM.vstr) (cr' : credit),
        regs_preserved R R' -> PM.vstr_at segs T3 M' o s -> PM.vs_size s = n ->
        (n <= 22 -> s = PM.VShort n) -> (23 <= n -> exists q, s = PM.VLong (PMSP.str_count n) n q) ->
        L5.bytes_at segs M' (PM.vs_data o s) l ->
        L5C.hpres L LB sp (PMSP.pm_scr 0) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PM.cost1 L (n + 16)) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (PM.vs_own s ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_str_ctor A) M model) K.

Definition iss_ctor_c_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (ois os sp r : Z) (s : PM.vstr) (b : bool) (l : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 4 ->
    getr R 10%bv = Z_to_bv 64 ois -> getr R 11%bv = Z_to_bv 64 os -> getr R 12%bv = Z_to_bv 64 8 ->
    sp <= ois -> ois + 272 <= os -> os + 24 <= hl_sptop L -> ois mod 8 = 0 -> os mod 8 = 0 -> L5.defined M ois 272 ->
    PM.vstr_at segs T3 M os s -> incl (PM.vs_own s) LB -> PM.vs_size s < 2 ^ 26 -> (forall c n q, s = PM.VLong c n q -> 23 <= n) ->
    Z.of_nat (length l) = PM.vs_size s -> L5.bytes_at segs M (PM.vs_data os s) l ->
    PMST.base_ok segs A M -> PMST.loc_ok segs A M b ->
    PMSP.credit_le (PM.cost1 L (PM.vs_size s + 32)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.vstr) (sm : PM.strm) (cr' : credit),
        regs_preserved R R' -> iss_at M' ois s' sm -> PM.vs_size s' = PM.vs_size s ->
        PM.sm_g sm = PM.vs_data (ois + 80) s' -> PM.sm_st sm = 0 ->
        L5.bytes_at segs M' (PM.vs_data (ois + 80) s') l ->
        PMST.loc_ok segs A M' true ->
        L5C.hpres L LB sp (PMSP.pm_scr 4) ((ois, 272) :: (if b then [] else PMSP.loc_W A)) M M' ->
        PMSP.credit_keep cr cr' (PM.cost1 L (PM.vs_size s + 32)) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (PM.vs_own s' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg R' r M' model') K) ->
    srealizes segs SCFG (cfg R (pa_iss_ctor A) M model) K.

Definition pay_in (PayOk : list byte -> Prop) : Prop :=
  forall payload, Z.of_nat (length payload) < 2 ^ 26 -> PayOk payload ->
  forall n, PESK.sp_hb P (s_hi (run n (map bv_unsigned payload) UbjRef.init)).
Definition pay_out (PayExport : list byte -> Prop) : Prop :=
  forall payload c, Z.of_nat (length payload) < 2 ^ 26 -> PESK.is_cap c -> (0 < c -> PESK.sp_cap P c) ->
  0 <= UbjRefFactsS8.F (map bv_unsigned payload) <= c -> PayExport payload.

End Specs.
End PECS.
