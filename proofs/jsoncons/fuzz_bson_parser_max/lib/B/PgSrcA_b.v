(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require LibIfaceAJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable FC : list Z.          (* [comment removed for export] *)

Abbreviation accA := (PMSPA.accA).
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation nullis_at := (PM.nullis_at segs A accA).
Abbreviation src_fields_at := (PM.src_fields_at segs accA).
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation pm_scr := PMSPA.pm_scr.
(* [comment removed for export] *)
Definition ffroomB (h : Z) (FF LK : list fframe) : Prop := forall k, In k FC -> Z.of_nat (ff_count k (FF ++ LK)) + h + 2 <= ff_cap k.
(* [comment removed for export] *)
Definition ofr (FF : list fframe) (lo hi : Z) : Prop := aobjA FF lo (hi - lo).

(* [comment removed for export] *)
Abbreviation W_srcfG := PGS.W_srcfG.
Abbreviation W_srcG := PGS.W_srcG.

(* [comment removed for export] *)
Abbreviation in_blk := PGS.in_blk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation owner := PGS.owner.
Abbreviation ow_at := PGS.ow_at.
Abbreviation ow_os := PGS.ow_os.
Abbreviation ow_ois := PGS.ow_ois.
Abbreviation ow_lo := PGS.ow_lo.
Abbreviation ow_hi := PGS.ow_hi.
Abbreviation ow_win := PGS.ow_win.

(* [comment removed for export] *)
Record owner_ok (O : owner) : Prop := {
  (* [comment removed for export] *)
  oo_src : forall M src OB, ow_at O M src OB ->
             src_fields_at M (ow_os O) (ow_ois O) (ow_ois O + 16) src /\ nullis_at M (ow_os O + 8) /\ L5.defined M (ow_os O) 296;
  (* [comment removed for export] *)
  oo_lay : ow_lo O <= ow_os O /\ ow_os O + 296 <= ow_hi O /\ ow_lo O <= ow_ois O /\ ow_ois O + 272 <= ow_hi O
           /\ ow_hi O <= ar_sptop ar /\ ow_os O mod 8 = 0 /\ ow_ois O mod 8 = 0 /\ 4096 <= ow_lo O
           /\ (ow_os O + 296 <= ow_ois O \/ ow_ois O + 272 <= ow_os O);
  (* [comment removed for export] *)
  oo_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst) (OB : list (Z * Z))
                  (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (VM : vml),
             ofr FF (ow_lo O) (ow_hi O) -> ow_at O M src OB ->
             (* [comment removed for export] *)
             ri_inv HI (PM.src_own src ++ OB ++ LBX) FF LK cr Aw M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= ow_lo O \/ ow_hi O <= fst b) (PM.src_own src ++ OB) ->
             (forall b, In b OB -> fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b) ->
             (* [comment removed for export] *)
             Forall (fun r => ((fst r + snd r <= ow_lo O \/ ow_hi O <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)
                               /\ app_mem (fst r) (snd r))      (* [comment removed for export] *)
                              \/ ow_win O M src OB (fst r) (snd r)) Wx ->
             L5CA.ahpres L ar (PM.src_own src ++ OB ++ LBX) FF sp scr (W_srcG (ow_os O) (ow_ois O) src ++ Wx) M M' ->
             src_fields_at M' (ow_os O) (ow_ois O) (ow_ois O + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             ow_at O M' src' OB;
  (* [comment removed for export] *)
  oo_win : forall M src OB p k, ow_at O M src OB -> ow_win O M src OB p k ->
             0 <= k /\ L5.defined M p k
             /\ (in_blk OB p k \/ (4096 <= p /\ p + k <= 2 ^ 47 /\ ow_lo O <= p /\ p + k <= ow_hi O /\ k < PM.CHUNK /\ (p + k <= ow_os O \/ ow_os O + 296 <= p)
                                   /\ (p + k <= ow_ois O \/ ow_ois O + 272 <= p)))
             /\ accA M p k      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_specG (pc h : Z)
           (args : owner -> list fframe -> bvmap 5 word -> (word -> option byte) -> Z -> PM.srcst -> list (Z * Z) -> Prop)
           (Wx : bvmap 5 word -> list L5.range -> Prop)
           (res : bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (O : owner), owner_ok O ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r : Z) (src : PM.srcst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    ri_inv HI (PM.src_own src ++ OB ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r h -> ffroomB h FF LK -> ffrsA FF sp -> ofr FF (ow_lo O) (ow_hi O) ->
    getr R 10%bv = Z_to_bv 64 (ow_os O) -> args O FF R M sp src OB -> Wx R Wextra ->
    ow_at O M src OB -> iss_at M (ow_ois O) str sm -> PMSTA.base_okA segs A M ->
    incl (PM.vs_own str) LBX ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        ow_at O M' src' OB ->
        iss_at M' (ow_ois O) str sm' -> PMSP.src_step src src' sm sm' ->
        res R R' M' src src' sm sm' ->
        L5CA.ahpres L ar (PM.src_own src ++ OB ++ LBX) FF sp (pm_scr h) (W_srcG (ow_os O) (ow_ois O) src ++ Wextra) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.src_own src ++ OB ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

Definition no_args (O : owner) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop := True.

(* [comment removed for export] *)
Definition fill_args (O : owner) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 (PM.sr_qc src) /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK.
Definition fill_buffer_specG : Prop := src_specG (pa_fill_buffer A) 3 fill_args PMSP.no_W PMPS.fill_res.

(* [comment removed for export] *)
Definition ignore_args (O : owner) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 1.
Definition peek_specG : Prop := src_specG (pa_peek A) 4 no_args PMSP.no_W PMPS.peek_res.
Definition ignore_specG : Prop := src_specG (pa_ignore A) 4 ignore_args PMSP.no_W PMPS.ignore_res.

(* [comment removed for export] *)
Definition dst_okG (O : owner) (FF : list fframe) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) (p k : Z) : Prop :=
  (aobjA FF p k /\ k <= 16 /\ L5.defined M p k /\ aacc M p k /\ (p + k <= ow_lo O \/ ow_hi O <= p)) \/ ow_win O M src OB p k.
Definition read_args (O : owner) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  exists p k, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 1 <= k <= PM.CHUNK /\ dst_okG O FF M sp src OB p k.
Definition src_read_specG : Prop := src_specG (pa_src_read A) 4 read_args PMPS.read_W PMPS.read_res.
Definition read_args_al (al : Z) (O : owner) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  sp mod 32 = al /\ read_args O FF R M sp src OB.
Definition src_read_specG_al (al : Z) : Prop := src_specG (pa_src_read A) 4 (read_args_al al) PMPS.read_W PMPS.read_res.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation towner := PGS.towner.
Abbreviation tw_at := PGS.tw_at.
Abbreviation tw_os := PGS.tw_os.
Abbreviation tw_ois := PGS.tw_ois.
Abbreviation tw_otb := PGS.tw_otb.
Abbreviation tw_lo := PGS.tw_lo.
Abbreviation tw_hi := PGS.tw_hi.
Abbreviation vstr_at := (PM.vstr_at segs accA).
Record towner_ok (T : towner) : Prop := {
  to_src : forall M src tb tg OB, tw_at T M src tb tg OB ->
             src_fields_at M (tw_os T) (tw_ois T) (tw_ois T + 16) src /\ nullis_at M (tw_os T + 8) /\ L5.defined M (tw_os T) 296
             /\ vstr_at M (tw_otb T) tb /\ PM.tb_ok tb tg;
  to_lay : tw_lo T <= tw_os T /\ tw_os T + 296 <= tw_hi T /\ tw_lo T <= tw_ois T /\ tw_ois T + 272 <= tw_hi T
           /\ tw_lo T <= tw_otb T /\ tw_otb T + 24 <= tw_hi T /\ tw_hi T <= ar_sptop ar /\ tw_hi T <= 2 ^ 47
           /\ tw_os T mod 8 = 0 /\ tw_ois T mod 8 = 0 /\ tw_otb T mod 8 = 0 /\ 4096 <= tw_lo T
           /\ (tw_os T + 296 <= tw_ois T \/ tw_ois T + 272 <= tw_os T)
           /\ (tw_otb T + 24 <= tw_os T \/ tw_os T + 296 <= tw_otb T) /\ (tw_otb T + 24 <= tw_ois T \/ tw_ois T + 272 <= tw_otb T);
  (* [comment removed for export] *)
  to_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst)
             (tb tb' : PM.vstr) (tg tg' : Z) (OB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (VM : vml),
             ofr FF (tw_lo T) (tw_hi T) -> tw_at T M src tb tg OB ->
             ri_inv HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) FF LK cr Aw M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= tw_lo T \/ tw_hi T <= fst b) (PM.src_own src ++ PM.vs_own tb ++ OB) ->
             (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                                   /\ (forall B' m', In (B', m') (PM.vs_own tb) -> fst b + snd b <= B' \/ B' + m' <= fst b)) ->
             (* [comment removed for export] *)
             Forall (fun r => (fst r + snd r <= tw_lo T \/ tw_hi T <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)
                              /\ app_mem (fst r) (snd r)) Wx ->      (* [comment removed for export] *)
             L5CA.ahpres L ar (OB ++ LBX) FF sp scr (W_srcfG (tw_os T) (tw_ois T) ++ [(tw_otb T, 24)] ++ Wx) M M' ->
             src_fields_at M' (tw_os T) (tw_ois T) (tw_ois T + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             vstr_at M' (tw_otb T) tb' -> PM.tb_ok tb' tg' ->
             tw_at T M' src' tb' tg' OB
}.
(* [comment removed for export] *)
Definition src_of_tw (T : towner) (tb : PM.vstr) (tg : Z) : owner :=
  {| ow_at := fun M src OB' => exists OB, OB' = PM.vs_own tb ++ OB /\ tw_at T M src tb tg OB;
     ow_os := tw_os T; ow_ois := tw_ois T; ow_lo := tw_lo T; ow_hi := tw_hi T;
     ow_win := fun M src OB' p k => 0 <= k /\ (((exists n, tb = PM.VShort n) /\ tw_otb T + 1 <= p /\ p + k <= tw_otb T + 24)
                                            \/ (exists c n q, tb = PM.VLong c n q /\ q <= p /\ p + k <= q + c)) |}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_span_specG (pc : Z) : Prop :=
  forall (T : towner), towner_ok T ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 6 -> ffroomB 6 FF LK -> ffrsA FF sp ->
    ofr FF (tw_lo T) (tw_hi T) ->
    getr R 10%bv = Z_to_bv 64 (tw_os T) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (tw_otb T) -> 0 <= len < 2 ^ 64 ->
    tw_at T M src tb tg OB -> iss_at M (tw_ois T) str sm -> PMSTA.base_okA segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 ->
    PMSP.credit_le (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tb tg)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        ((ptr = 0 /\ n = 0) \/ in_blk (PM.src_own src' ++ PM.vs_own tb' ++ OB) ptr n \/ (tw_otb T + 1 <= ptr /\ ptr + n <= tw_otb T + 24)) ->
        L5.defined M' ptr n -> accA M' ptr n ->
        tw_at T M' src' tb' tg' OB -> iss_at M' (tw_ois T) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 6) (W_srcfG (tw_os T) (tw_ois T) ++ [(tw_otb T, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tb tg)) (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tb' tg')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition srd_read_specG (pc : Z) : Prop :=
  forall (T : towner), towner_ok T ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (str : PM.vstr) (sm : PM.strm),
    ri_inv HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 5 -> ffroomB 5 FF LK -> ffrsA FF sp ->
    ofr FF (tw_lo T) (tw_hi T) ->
    getr R 10%bv = Z_to_bv 64 (tw_os T) -> getr R 11%bv = Z_to_bv 64 (tw_otb T) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    tw_at T M src tb tg OB -> iss_at M (tw_ois T) str sm -> PMSTA.base_okA segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> PM.vs_size tb + PM.unread src sm < 2 ^ 26 ->
    PMSP.credit_le (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tb tg)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
            (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed src src' sm sm' = d -> PM.vs_size tb' = PM.vs_size tb + d ->
        tw_at T M' src' tb' tg' OB -> iss_at M' (tw_ois T) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 5) (W_srcfG (tw_os T) (tw_ois T) ++ [(tw_otb T, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tb tg)) (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) tb' tg')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition tbfill_args (O : owner) (FF : list fframe) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK /\ ow_win O M src OB p PM.CHUNK.   (* [comment removed for export] *)
Definition fill_buffer_tb_specG : Prop := src_specG (pa_fill_buffer A) 3 tbfill_args PMTXS.tbfill_W PMTXS.tbfill_res.

End Specs.
End PGSA.
