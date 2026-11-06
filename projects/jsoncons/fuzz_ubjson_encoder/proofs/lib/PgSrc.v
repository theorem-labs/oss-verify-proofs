(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PmParSpecs PmTxtSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation iss_at := (PM.iss_at segs A PMSP.T3).
Abbreviation nullis_at := (PM.nullis_at segs A PMSP.T3).
Abbreviation src_fields_at := (PM.src_fields_at segs PMSP.T3).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.

(* [comment removed for export] *)
Definition W_srcfG (os ois : Z) : list L5.range := [(os + 256, 40); (ois + 40, 8); (ois + 152, 4)].
Definition W_srcG (os ois : Z) (src : PM.srcst) : list L5.range := W_srcfG os ois ++ [(PM.sr_qc src, PM.CHUNK)].

(* [comment removed for export] *)
Definition in_blk (LB : list (Z * Z)) (p k : Z) : Prop := exists B m, In (B, m) LB /\ B <= p /\ p + k <= B + m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record owner : Type := OWN {
  ow_at  : (word -> option byte) -> PM.srcst -> list (Z * Z) -> Prop;   (* [comment removed for export] *)
  ow_os  : Z;                                                          (* [comment removed for export] *)
  ow_ois : Z;                                                          (* [comment removed for export] *)
  ow_lo  : Z;                                                          (* [comment removed for export] *)
  ow_hi  : Z;                                                          (* [comment removed for export] *)
  ow_win : (word -> option byte) -> PM.srcst -> list (Z * Z) -> Z -> Z -> Prop   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record owner_ok (O : owner) : Prop := {
  (* [comment removed for export] *)
  oo_src : forall M src OB, ow_at O M src OB ->
             src_fields_at M (ow_os O) (ow_ois O) (ow_ois O + 16) src /\ nullis_at M (ow_os O + 8) /\ L5.defined M (ow_os O) 296;
  (* [comment removed for export] *)
  oo_lay : ow_lo O <= ow_os O /\ ow_os O + 296 <= ow_hi O /\ ow_lo O <= ow_ois O /\ ow_ois O + 272 <= ow_hi O
           /\ ow_hi O <= hl_sptop L /\ ow_os O mod 8 = 0 /\ ow_ois O mod 8 = 0 /\ 4096 <= ow_lo O
           /\ (ow_os O + 296 <= ow_ois O \/ ow_ois O + 272 <= ow_os O);
  (* [comment removed for export] *)
  oo_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst) (OB : list (Z * Z))
                  (cr : credit) (VM : VmMaps),
             sp <= ow_lo O -> ow_at O M src OB ->
             (* [comment removed for export] *)
             hi_heap HI (PM.src_own src ++ OB ++ LBX) cr M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= ow_lo O \/ ow_hi O <= fst b) (PM.src_own src ++ OB) ->
             (forall b, In b OB -> fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b) ->
             (* [comment removed for export] *)
             Forall (fun r => ((fst r + snd r <= ow_lo O \/ ow_hi O <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r))
                              \/ ow_win O M src OB (fst r) (snd r)) Wx ->
             L5C.hpres L (PM.src_own src ++ OB ++ LBX) sp scr (W_srcG (ow_os O) (ow_ois O) src ++ Wx) M M' ->
             src_fields_at M' (ow_os O) (ow_ois O) (ow_ois O + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             ow_at O M' src' OB;
  (* [comment removed for export] *)
  oo_win : forall M src OB p k, ow_at O M src OB -> ow_win O M src OB p k ->
             0 <= k /\ L5.defined M p k
             /\ (in_blk OB p k \/ (4096 <= p /\ p + k <= 2 ^ 47 /\ ow_lo O <= p /\ p + k <= ow_hi O /\ k < PM.CHUNK /\ (p + k <= ow_os O \/ ow_os O + 296 <= p)
                                   /\ (p + k <= ow_ois O \/ ow_ois O + 272 <= p)))
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_specG (pc h : Z)
           (args : owner -> bvmap 5 word -> (word -> option byte) -> Z -> PM.srcst -> list (Z * Z) -> Prop)
           (Wx : bvmap 5 word -> list L5.range -> Prop)
           (res : bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (O : owner), owner_ok O ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r : Z) (src : PM.srcst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    hi_heap HI (PM.src_own src ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> sp <= ow_lo O ->
    getr R 10%bv = Z_to_bv 64 (ow_os O) -> args O R M sp src OB -> Wx R Wextra ->
    ow_at O M src OB -> iss_at M (ow_ois O) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        ow_at O M' src' OB ->
        iss_at M' (ow_ois O) str sm' -> PMSP.src_step src src' sm sm' ->
        res R R' M' src src' sm sm' ->
        L5C.hpres L (PM.src_own src ++ OB ++ LBX) sp (pm_scr h) (W_srcG (ow_os O) (ow_ois O) src ++ Wextra) M M' ->
        hi_heap HI (PM.src_own src ++ OB ++ LBX) cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

Definition no_args (O : owner) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop := True.

(* [comment removed for export] *)
Definition fill_args (O : owner) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 (PM.sr_qc src) /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK.
Definition fill_buffer_specG : Prop := src_specG (pa_fill_buffer A) 3 fill_args PMSP.no_W PMPS.fill_res.

(* [comment removed for export] *)
Definition ignore_args (O : owner) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 1.
Definition peek_specG : Prop := src_specG (pa_peek A) 4 no_args PMSP.no_W PMPS.peek_res.
Definition ignore_specG : Prop := src_specG (pa_ignore A) 4 ignore_args PMSP.no_W PMPS.ignore_res.

(* [comment removed for export] *)
Definition dst_okG (O : owner) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) (p k : Z) : Prop :=
  (sp <= p /\ p + k <= ow_lo O /\ k <= 16 /\ L5.defined M p k) \/ ow_win O M src OB p k.
Definition read_args (O : owner) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  exists p k, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 1 <= k <= PM.CHUNK /\ dst_okG O M sp src OB p k.
Definition src_read_specG : Prop := src_specG (pa_src_read A) 4 read_args PMPS.read_W PMPS.read_res.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record towner : Type := TOWN {
  tw_at  : (word -> option byte) -> PM.srcst -> PM.vstr -> Z -> list (Z * Z) -> Prop;
  tw_os  : Z; tw_ois : Z; tw_otb : Z; tw_lo : Z; tw_hi : Z
}.
Abbreviation vstr_at := (PM.vstr_at segs PMSP.T3).
Record towner_ok (T : towner) : Prop := {
  to_src : forall M src tb tg OB, tw_at T M src tb tg OB ->
             src_fields_at M (tw_os T) (tw_ois T) (tw_ois T + 16) src /\ nullis_at M (tw_os T + 8) /\ L5.defined M (tw_os T) 296
             /\ vstr_at M (tw_otb T) tb /\ PM.tb_ok tb tg;
  to_lay : tw_lo T <= tw_os T /\ tw_os T + 296 <= tw_hi T /\ tw_lo T <= tw_ois T /\ tw_ois T + 272 <= tw_hi T
           /\ tw_lo T <= tw_otb T /\ tw_otb T + 24 <= tw_hi T /\ tw_hi T <= hl_sptop L /\ tw_hi T <= 2 ^ 47
           /\ tw_os T mod 8 = 0 /\ tw_ois T mod 8 = 0 /\ tw_otb T mod 8 = 0 /\ 4096 <= tw_lo T
           /\ (tw_os T + 296 <= tw_ois T \/ tw_ois T + 272 <= tw_os T)
           /\ (tw_otb T + 24 <= tw_os T \/ tw_os T + 296 <= tw_otb T) /\ (tw_otb T + 24 <= tw_ois T \/ tw_ois T + 272 <= tw_otb T);
  (* [comment removed for export] *)
  to_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst)
             (tb tb' : PM.vstr) (tg tg' : Z) (OB : list (Z * Z)) (cr : credit) (VM : VmMaps),
             sp <= tw_lo T -> tw_at T M src tb tg OB ->
             hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= tw_lo T \/ tw_hi T <= fst b) (PM.src_own src ++ PM.vs_own tb ++ OB) ->
             (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                                   /\ (forall B' m', In (B', m') (PM.vs_own tb) -> fst b + snd b <= B' \/ B' + m' <= fst b)) ->
             (* [comment removed for export] *)
             Forall (fun r => (fst r + snd r <= tw_lo T \/ tw_hi T <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)) Wx ->
             L5C.hpres L (OB ++ LBX) sp scr (W_srcfG (tw_os T) (tw_ois T) ++ [(tw_otb T, 24)] ++ Wx) M M' ->
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
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 6 ->
    sp <= tw_lo T ->
    getr R 10%bv = Z_to_bv 64 (tw_os T) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (tw_otb T) -> 0 <= len < 2 ^ 64 ->
    tw_at T M src tb tg OB -> iss_at M (tw_ois T) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 ->
    PMSP.credit_le (PM.pot_text L tb tg) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        ((ptr = 0 /\ n = 0) \/ in_blk (PM.src_own src' ++ PM.vs_own tb' ++ OB) ptr n \/ (tw_otb T + 1 <= ptr /\ ptr + n <= tw_otb T + 24)) ->
        L5.defined M' ptr n ->
        tw_at T M' src' tb' tg' OB -> iss_at M' (tw_ois T) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 6) (W_srcfG (tw_os T) (tw_ois T) ++ [(tw_otb T, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PM.pot_text L tb tg) (PM.pot_text L tb' tg') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition srd_read_specG (pc : Z) : Prop :=
  forall (T : towner), towner_ok T ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 5 ->
    sp <= tw_lo T ->
    getr R 10%bv = Z_to_bv 64 (tw_os T) -> getr R 11%bv = Z_to_bv 64 (tw_otb T) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    tw_at T M src tb tg OB -> iss_at M (tw_ois T) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> PM.vs_size tb + PM.unread src sm < 2 ^ 26 ->
    PMSP.credit_le (PM.pot_text L tb tg) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
            (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed src src' sm sm' = d -> PM.vs_size tb' = PM.vs_size tb + d ->
        tw_at T M' src' tb' tg' OB -> iss_at M' (tw_ois T) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 5) (W_srcfG (tw_os T) (tw_ois T) ++ [(tw_otb T, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PM.pot_text L tb tg) (PM.pot_text L tb' tg') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition tbfill_args (O : owner) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK /\ ow_win O M src OB p PM.CHUNK.   (* [comment removed for export] *)
Definition fill_buffer_tb_specG : Prop := src_specG (pa_fill_buffer A) 3 tbfill_args PMTXS.tbfill_W PMTXS.tbfill_res.

End Specs.
End PGS.
