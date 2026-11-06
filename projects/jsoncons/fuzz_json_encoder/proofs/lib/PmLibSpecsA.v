(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mem := (word -> option byte).
Definition fp_ok (fx : FPState) : Prop := FPSteps.frm_zero (@fp_csr fx).

Section SpecsA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.          (* [comment removed for export] *)

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : mem) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) model.
Definition a0 (R : bvmap 5 word) (v : Z) : Prop := getr R 10%bv = Z_to_bv 64 v.
Definition a1 (R : bvmap 5 word) (v : Z) : Prop := getr R 11%bv = Z_to_bv 64 v.
Definition a2 (R : bvmap 5 word) (v : Z) : Prop := getr R 12%bv = Z_to_bv 64 v.
Definition a3 (R : bvmap 5 word) (v : Z) : Prop := getr R 13%bv = Z_to_bv 64 v.
Definition u64 (M : mem) (a v : Z) : Prop := L5.u64_at (hl_segs L) M a v.
Definition u8 (M : mem) (a v : Z) : Prop := L5.u8_at (hl_segs L) M a v.

(* [comment removed for export] *)
Definition ainfr (FF : list fframe) (a n : Z) : Prop := CL5A.ainfr FF a n.
(* [comment removed for export] *)
Definition acobj (FF : list fframe) (sp a n : Z) : Prop := CL5A.acobj ar FF sp a n.

(* [comment removed for export] *)
Definition cps_asan (pc r sp scr : Z) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (d : Z)
           (Pre : bvmap 5 word -> mem -> Prop)
           (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] -> fp_ok fx ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    CHA.astk ar M sp scr -> CHA.ffroom FF LK d -> CHA.ffrs FF sp -> Pre R M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
            (LK' : list fframe) (A' : list (Z * Z)),
        fp_ok fx' -> Post R M R' M' LB' cr' LBk W -> regs_preserved R R' ->
        CHA.ahpres L ar LBk FF sp scr W M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) SCFG (@cfg fx' R' r M' model') K) ->
    srealizes (hl_segs L) SCFG (@cfg fx R pc M model) K.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a4 (R : bvmap 5 word) (v : Z) : Prop := getr R 14%bv = Z_to_bv 64 v.
Definition u32 (M : mem) (a v : Z) : Prop := L5.u32_at (hl_segs L) M a v.
Definition MALLOC_SCR : Z := 4096.      (* [comment removed for export] *)
Definition SM_SCR : Z := 512.           (* [comment removed for export] *)
Definition MEM_SCR : Z := 2560.         (* [comment removed for export] *)
Definition ANNOT_SCR : Z := 4096.       (* [comment removed for export] *)
Definition MEMCMP_SCR : Z := 8192.      (* [comment removed for export] *)
Definition CXA_SCR : Z := 512.          (* [comment removed for export] *)
Definition STRTOD_SCR : Z := PML.STRTOD_SCR_V.   (* [comment removed for export] *)
Definition OPNEW_SCR : Z := 16 + MALLOC_SCR.
Definition OPDEL_SCR : Z := MALLOC_SCR.
Definition STR_SCR : Z := 256 + OPNEW_SCR.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fobj := PMLA.fobj.
Definition stksh := PMLA.stksh ar.
Definition afresh := PMLA.afresh L ar.

(* [comment removed for export] *)
Definition opnew_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n sp r : Z),
    cps_asan pc r sp OPNEW_SCR LB FF LK cr A 0
      (fun R M => a0 R n /\ 0 < n <= 2 ^ 27 /\ acredit_ok L cr n)
      (fun R M R' M' LB' cr' LBk W => exists q, a0 R' q /\ afresh LB FF M' q n /\ LB' = (q, n) :: LB /\ cr' = adebit L cr n /\ LBk = LB /\ W = []).
(* [comment removed for export] *)
Definition opdel_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (q n sp r : Z),
    cps_asan pc r sp OPDEL_SCR LB FF LK cr A 0
      (fun R M => a0 R q /\ In (q, n) LB)
      (fun R M R' M' LB' cr' LBk W => LB' = lb_remove q LB /\ cr' = cr /\ LBk = lb_remove q LB /\ W = []).
(* [comment removed for export] *)
Definition opdel_null_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r : Z),
    cps_asan pc r sp OPDEL_SCR LB FF LK cr A 0
      (fun R M => a0 R 0)
      (fun R M R' M' LB' cr' LBk W => LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
Definition set_shadow_spec (pc v : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (f : fframe) (sa n sp r : Z),
    cps_asan pc r sp 256 LB FF LK cr A 0
      (fun R M => a0 R sa /\ a1 R n /\ In f FF /\ 0 <= n /\ S (ff_addr f) <= sa /\ sa + n <= S (ff_addr f) + ff_bytes (ff_class f) / 8)
      (fun R M R' M' LB' cr' LBk W => (forall j, 0 <= j < n -> byte_at M' (sa + j) v) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(sa, n)]).

(* [comment removed for export] *)
Definition cstatic (a n : Z) : Prop := forall x, a <= x < a + n -> hl_img_lo L <= x < hl_img_hi L /\ ~ hl_rt_static L x /\ ~ hl_rt_ro L x.

(* [comment removed for export] *)
Definition guard_acquire_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (G sp r : Z),
    cps_asan pc r sp 64 LB FF LK cr A 0
      (fun R M => a0 R G /\ 0 <= G < 2 ^ 62 (* [comment removed for export] *) /\ u8 M G 0 /\ u8 M (G + 1) 0 /\ cstatic G 2 /\ L5.writable (hl_segs L) M G 2)
      (fun R M R' M' LB' cr' LBk W => a0 R' 1 /\ u8 M' G 0 /\ u8 M' (G + 1) 2 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(G, 2)]).
Definition guard_release_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (G sp r : Z),
    cps_asan pc r sp 64 LB FF LK cr A 0
      (fun R M => a0 R G /\ 0 <= G < 2 ^ 62 (* [comment removed for export] *) /\ cstatic G 2 /\ L5.writable (hl_segs L) M G 2)
      (fun R M R' M' LB' cr' LBk W => u8 M' G 1 /\ u8 M' (G + 1) 1 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(G, 2)]).
(* [comment removed for export] *)
Definition system_category_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r : Z),
    cps_asan pc r sp 128 LB FF LK cr A 0
      (fun R M => PMLA.img_ro IC M /\ cstatic (PMLA.SYSCAT_GUARD IC) 2 /\
                  ((u8 M (PMLA.SYSCAT_GUARD IC) 0 /\ u8 M (PMLA.SYSCAT_GUARD IC + 1) 0) \/ u8 M (PMLA.SYSCAT_GUARD IC) 1))
      (fun R M R' M' LB' cr' LBk W => a0 R' (PMLA.OBJ_SYSTEM_CATEGORY IC) /\ u8 M' (PMLA.SYSCAT_GUARD IC) 1 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(PMLA.SYSCAT_GUARD IC, 2)]).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strtod_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s endp sp r : Z) (txt : list Z),
    cps_asan pc r sp STRTOD_SCR LB FF LK cr A 0
      (fun R M => a0 R s /\ a1 R endp /\ PMLA.img_ro IC M /\
                  L5.bytes_at (hl_segs L) M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ PML.num_final txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M endp 8 /\ acobj FF sp endp 8 /\
                  (s + Z.of_nat (length txt) + 1 <= sp - STRTOD_SCR \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= endp \/ endp + 8 <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= hl_tp L - 164 \/ hl_tp L - 160 <= s) /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\
                  (exists b, In b LB /\ fst b <= s /\ s + Z.of_nat (length txt) + 1 <= fst b + snd b))       (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => u64 M' endp (s + Z.of_nat (length txt)) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(endp, 8); (hl_tp L - 164, 4)]).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vec_at (M : mem) (o b len cap : Z) : Prop := u64 M o b /\ u64 M (o + 8) (b + len) /\ u64 M (o + 16) (b + cap).
(* [comment removed for export] *)
Definition vec_ok (M : mem) (LB : list (Z * Z)) (FF : list fframe) (o b len cap : Z) : Prop :=
  vec_at M o b len cap /\ ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
  In (b, cap) LB /\ 0 <= len <= cap /\ 0 < cap <= 4096 /\ shadow_cont M b cap len.

Definition AINC_SCR : Z := 4112.      (* [comment removed for export] *)
Definition VSLOW_SCR : Z := 8192.     (* [comment removed for export] *)
Definition VPUSH_SCR : Z := 48 + VSLOW_SCR.
Definition POP_SCR : Z := 96 + 32 + 4112.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition annotate_increase_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b len cap n sp r : Z),
    cps_asan pc r sp AINC_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R n /\ vec_at M o b len cap /\ ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, cap) LB /\ 0 <= len /\ 0 < n /\ len + n <= cap /\ shadow_cont M b cap len /\ b <> 0 /\ cap <= 4096)     (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap (len + n) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).
(* [comment removed for export] *)
Definition annotate_shrink_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b len old cap sp r : Z),
    cps_asan pc r sp AINC_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R old /\ vec_at M o b len cap /\ ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, cap) LB /\ 0 <= len <= old /\ old <= cap /\ shadow_cont M b cap old /\ b <> 0 /\ cap <= 4096)            (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap len /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).

(* [comment removed for export] *)
Definition afresh_cont (LB : list (Z * Z)) (FF : list fframe) (M' : mem) (q n len : Z) : Prop :=
  ablock_range L ar q n /\ blocks_apart q n LB /\ fframes_apart q n FF /\ L5.defined M' q n /\ shadow_cont M' q n len.

(* [comment removed for export] *)
Definition vec_push_slow_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b cap xa x sp r : Z) (st : list Z),
    cps_asan pc r sp VSLOW_SCR LB FF LK cr A 4
      (fun R M => a0 R o /\ a1 R xa /\ vec_ok M LB FF o b cap cap /\ Z.of_nat (length st) = cap /\ L5.bytes_at (hl_segs L) M b st /\
                  u8 M xa x /\ acobj FF sp xa 1 /\ aacc M xa 1 /\ (xa + 1 <= o \/ o + 24 <= xa) /\ acredit_ok L cr (2 * cap) /\ 2 * cap <= 4096 /\   (* [comment removed for export] *)
                  stksh M sp VSLOW_SCR /\ 4 <= cap)     (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => exists b',
          a0 R' (b' + cap + 1) /\ vec_at M' o b' (cap + 1) (2 * cap) /\ L5.bytes_at (hl_segs L) M' b' (st ++ [x]) /\
          afresh_cont (lb_remove b LB) FF M' b' (2 * cap) (cap + 1) /\
          LB' = (b', 2 * cap) :: lb_remove b LB /\ cr' = adebit L cr (2 * cap) /\ LBk = lb_remove b LB /\ W = [(o, 24)]).

(* [comment removed for export] *)
Definition vec_push_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b cap xa x sp r : Z) (st : list Z),
    cps_asan pc r sp VPUSH_SCR LB FF LK cr A 4
      (fun R M => a0 R o /\ a1 R xa /\ vec_ok M LB FF o b (Z.of_nat (length st)) cap /\ L5.bytes_at (hl_segs L) M b st /\
                  u8 M xa x /\ acobj FF sp xa 1 /\ aacc M xa 1 /\ (xa + 1 <= o \/ o + 24 <= xa) /\
                  (Z.of_nat (length st) = cap -> acredit_ok L cr (2 * cap) /\ 2 * cap <= 4096 /\ 4 <= cap) /\ stksh M sp VPUSH_SCR)            (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = lb_remove b LB /\
          ((Z.of_nat (length st) < cap /\ vec_at M' o b (Z.of_nat (length st) + 1) cap /\ L5.bytes_at (hl_segs L) M' b (st ++ [x]) /\
            shadow_cont M' b cap (Z.of_nat (length st) + 1) /\ LB' = LB /\ cr' = cr)
        \/ (Z.of_nat (length st) = cap /\ exists b', vec_at M' o b' (cap + 1) (2 * cap) /\ L5.bytes_at (hl_segs L) M' b' (st ++ [x]) /\
            afresh_cont (lb_remove b LB) FF M' b' (2 * cap) (cap + 1) /\
            LB' = (b', 2 * cap) :: lb_remove b LB /\ cr' = adebit L cr (2 * cap)))).

(* [comment removed for export] *)
Definition pop_state_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P b cap x sp r : Z) (rest : list Z),
    cps_asan pc r sp POP_SCR LB FF LK cr A 2
      (fun R M => a0 R P /\ sp mod 32 = 0 /\ vec_ok M LB FF (P + 248) b (Z.of_nat (length rest) + 1) cap /\ L5.bytes_at (hl_segs L) M b (rest ++ [x]) /\ 0 <= x < 256)
      (fun R M R' M' LB' cr' LBk W => a0 R' x /\ vec_at M' (P + 248) b (Z.of_nat (length rest)) cap /\ shadow_cont M' b cap (Z.of_nat (length rest)) /\
          LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(P + 256, 8); (S b, (cap + 7) / 8)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ANEW_SCR : Z := 32 + ANNOT_SCR.      (* [comment removed for export] *)
Definition annotate_new_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b cap n sp r : Z),
    cps_asan pc r sp ANEW_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R n /\ u64 M o b /\ u64 M (o + 16) (b + cap) /\ acobj FF sp o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, cap) LB /\ 0 <= n <= cap /\ cap <= 4096 /\ shadow_cont M b cap cap /\ b <> 0)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap n /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).
(* [comment removed for export] *)
Definition annotate_delete_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b len cap sp r : Z),
    cps_asan pc r sp ANEW_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ vec_at M o b len cap /\ acobj FF sp o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  In (b, cap) LB /\ 0 <= len <= cap /\ cap <= 4096 /\ shadow_cont M b cap len /\ b <> 0)
      (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap cap /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).

(* [comment removed for export] *)
Definition annotate_delete_null_spec (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    cps_asan pc r sp ANEW_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ u64 M o 0 /\ u64 M (o + 8) 0 /\ u64 M (o + 16) 0 (* [comment removed for export] *) /\ acobj FF sp o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3)
      (fun R M R' M' LB' cr' LBk W => LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

Definition VRES_SCR : Z := 8192.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition vec_reserve_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    cps_asan pc r sp VRES_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R 66 /\ u64 M o 0 /\ u64 M (o + 8) 0 /\ u64 M (o + 16) 0 /\ ainfr FF o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\
                  stksh M sp VRES_SCR /\ acredit_ok L cr 66)
      (fun R M R' M' LB' cr' LBk W => exists b, vec_at M' o b 0 66 /\ afresh_cont LB FF M' b 66 0 /\
                                                LB' = (b, 66) :: LB /\ cr' = adebit L cr 66 /\ LBk = LB /\ W = [(o, 24)]).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vec_dtor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (t o b len cap sp r : Z),
    cps_asan pc r sp (64 + ANEW_SCR) LB FF LK cr A 0
      (fun R M => a0 R t /\ u64 M t o /\ acobj FF sp t 8 /\ t mod 8 = 0 /\ shadow_zero M t 1 /\ (t + 8 <= o \/ o + 24 <= t) /\ vec_ok M LB FF o b len cap)
      (fun R M R' M' LB' cr' LBk W => LB' = lb_remove b LB /\ cr' = cr /\ LBk = lb_remove b LB /\ W = [(o, 24)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition str_at := PMLA.str_at (hl_segs L).
Definition str_at_w := PMLA.str_at_w (hl_segs L).
(* [comment removed for export] *)
Definition str_reserve_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    cps_asan pc r sp STR_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R 256 /\ u64 M o 0 /\ u64 M (o + 8) 0 /\ u64 M (o + 16) 0 (* [comment removed for export] *) /\
                  fobj M FF o 24 /\ stksh M sp STR_SCR /\ acredit_ok L cr 264)
      (fun R M R' M' LB' cr' LBk W => exists p, str_at M' o (PML.SLong 264 p []) /\ afresh LB FF M' p 264 /\
                                                LB' = (p, 264) :: LB /\ cr' = adebit L cr 264 /\ LBk = LB /\ W = [(o, 24)]).
(* [comment removed for export] *)
Definition str_grownA (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M' : mem) (o cap p : Z) (s' : list Z)
           (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) : Prop :=
     (str_at M' o (PML.SLong cap p s') /\ shadow_blk M' p cap /\ LB' = LB /\ cr' = cr /\ LBk = lb_remove p LB)
  \/ (exists p', let cap' := PML.grow_cap cap (Z.of_nat (length s')) in
        cap <= Z.of_nat (length s') /\
        str_at M' o (PML.SLong cap' p' s') /\ afresh (lb_remove p LB) FF M' p' cap' /\
        LB' = (p', cap') :: lb_remove p LB /\ cr' = adebit L cr cap' /\ LBk = lb_remove p LB).
(* [comment removed for export] *)
Definition str_push_back_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o cap p c sp r : Z) (s : list Z),
    cps_asan pc r sp STR_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R c /\ 0 <= c < 256 /\ str_at M o (PML.SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ shadow_blk M p cap /\ fobj M FF o 24 /\
                  stksh M sp STR_SCR /\ Z.of_nat (length s) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + 1 -> acredit_ok L cr (PML.grow_cap cap (Z.of_nat (length s) + 1))))
      (fun R M R' M' LB' cr' LBk W => str_grownA LB FF cr M' o cap p (s ++ [c]) LB' cr' LBk /\ W = [(o, 24)]).
(* [comment removed for export] *)
Definition str_src_ok (M : mem) (LB : list (Z * Z)) (p q : Z) (src : list Z) : Prop :=
  L5.bytes_at (hl_segs L) M q src /\ L5.defined M q (Z.of_nat (length src)) /\ aacc M q (Z.of_nat (length src)) /\
  exists b, In b LB /\ fst b <> p /\ fst b <= q /\ q + Z.of_nat (length src) <= fst b + snd b.
Definition str_append_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o cap p q sp r : Z) (s src : list Z),
    cps_asan pc r sp STR_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R q /\ a2 R (Z.of_nat (length src)) /\
                  str_at M o (PML.SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ shadow_blk M p cap /\ fobj M FF o 24 /\ stksh M sp STR_SCR /\
                  (src = [] \/ str_src_ok M LB p q src) /\
                  Z.of_nat (length s) + Z.of_nat (length src) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + Z.of_nat (length src) -> acredit_ok L cr (PML.grow_cap cap (Z.of_nat (length s) + Z.of_nat (length src)))))
      (fun R M R' M' LB' cr' LBk W => str_grownA LB FF cr M' o cap p (s ++ src) LB' cr' LBk /\ W = [(o, 24)]).
(* [comment removed for export] *)
Definition APPR_SCR : Z := 512 + STR_SCR.
Definition str_append_range_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o cap p q sp r : Z) (s src : list Z),
    cps_asan pc r sp APPR_SCR LB FF LK cr A 2
      (fun R M => a0 R o /\ a1 R q /\ a2 R (q + Z.of_nat (length src)) /\ sp mod 32 = 0 /\
                  str_at M o (PML.SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ shadow_blk M p cap /\ fobj M FF o 24 /\ stksh M sp APPR_SCR /\
                  str_src_ok M LB p q src /\
                  Z.of_nat (length s) + Z.of_nat (length src) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + Z.of_nat (length src) -> acredit_ok L cr (PML.grow_cap cap (Z.of_nat (length s) + Z.of_nat (length src)))))
      (fun R M R' M' LB' cr' LBk W => str_grownA LB FF cr M' o cap p (s ++ src) LB' cr' LBk /\ W = [(o, 24)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SETEC_SCR : Z := 1024.                   (* [comment removed for export] *)
Definition PARENT_SCR : Z := 640.                   (* [comment removed for export] *)
Definition AFTERV_SCR : Z := 128 + SETEC_SCR.       (* [comment removed for export] *)
Definition ESV_SCR : Z := 256 + POP_SCR.            (* [comment removed for export] *)
Definition CONVERT_SCR : Z := 128 + STR_SCR.        (* [comment removed for export] *)
Definition APPEND_CP_SCR : Z := 128 + SETEC_SCR.    (* [comment removed for export] *)
Definition DECSTR_SCR : Z := 176 + STRTOD_SCR.      (* [comment removed for export] *)
Definition ENDNUM_SCR : Z := 160 + DECSTR_SCR.      (* [comment removed for export] *)
Definition PF_SCR : Z := 512 + ENDNUM_SCR.          (* [comment removed for export] *)
Definition SKIPWS_SCR : Z := 160 + PF_SCR.          (* [comment removed for export] *)
Definition PSOME_SCR : Z := 704 + PF_SCR.           (* [comment removed for export] *)
Definition READNEXT_SCR : Z := 224 + PSOME_SCR.     (* [comment removed for export] *)
Definition READ_SCR : Z := 32 + READNEXT_SCR.
Definition CTOR_SCR : Z := 1024 + VPUSH_SCR.        (* [comment removed for export] *)
Definition RCTOR_SCR : Z := 176 + CTOR_SCR.
Definition ISLAND_SCR : Z := 2048 + MEMCMP_SCR.     (* [comment removed for export] *)
Definition ISS_SCR : Z := 512 + ISLAND_SCR.
Definition PDTOR_SCR : Z := 160 + AINC_SCR.
Definition SDTOR_SCR : Z := 128 + MALLOC_SCR.
Definition LIB_SCR : Z := 176 + Z.max READ_SCR (Z.max RCTOR_SCR ISS_SCR).     (* [comment removed for export] *)

Definition pstate := PML.pstate.
Definition parser_at := PMLA.parser_at (hl_segs L) IC.
Definition parser_sh := PMLA.parser_sh.
Definition vis_at := PMLA.vis_at (hl_segs L) IC.
Definition ec_at := PMLA.ec_at (hl_segs L) IC.
Definition ls_ok := PMLA.ls_ok (hl_segs L) IC.
Definition win_okA := PMLA.win_okA.

(* [comment removed for export] *)
Definition ptrans_gbA (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : pstate),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo) FF LK cr A d
      (fun R M => Args R M LBo P V E ps /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  PMLA.pcredit_xA L cr ps kx bx /\ fobj M FF P 272 /\ fobj M FF V 8 /\ fobj M FF E 16 /\
                  PMLA.apart P 272 V 8 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 8 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMLA.W_parA IC P E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R').
Definition ptrans_gA := ptrans_gbA PML.wf_ps PML.buf_bound.
Definition buf_bound_stale (ps : pstate) (B : Z) : Prop := Z.of_nat (length (PML.ps_buf ps)) + PML.winlen ps <= B /\ B < 2 ^ 26 /\ 0 <= PML.winlen ps.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptransA := ptrans_gA parser_at (fun _ => parser_at).
Definition ptrans_curA := ptrans_gA parser_at (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps))).
Definition ptrans_staleA (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbA PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
               (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.
(* [comment removed for export] *)
Definition ptrans_gbkA (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : pstate),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo) FF LK cr A d
      (fun R M => Args R M LBo P V E ps /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  PMLA.pcredit_xA L cr ps kx bx /\ fobj M FF P 272 /\ fobj M FF V 8 /\ fobj M FF E 16 /\
                  PMLA.apart P 272 V 8 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 8 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = PML.ps_blocks ps ++ LBo /\ W = PMLA.W_parA IC P E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R' /\
          PML.ps_blocks ps' = PML.ps_blocks ps).
Definition ptrans_stalekA (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbkA PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
                (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.
(* [comment removed for export] *)
Definition W_parE (P E : Z) : list L5.range := [(P, 272); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)].
Lemma W_parE_app : forall P E, W_parE P E = PMLA.W_parA IC P E ++ [(hl_tp L - 164, 4)].
Proof. intros; reflexivity. Qed.
Definition ptrans_gbeA (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E B kx bx : Z) (g : PML.ls_state) (ps : pstate),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo) FF LK cr A d
      (fun R M => Args R M LBo P V E ps /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  PMLA.pcredit_xA L cr ps kx bx /\ fobj M FF P 272 /\ fobj M FF V 8 /\ fobj M FF E 16 /\
                  PMLA.apart P 272 V 8 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 8 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = W_parE P E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R').
Definition ptrans_geA := ptrans_gbeA PML.wf_ps PML.buf_bound.
Definition ptranseA := ptrans_geA parser_at (fun _ => parser_at).
Definition ptrans_cureA := ptrans_geA parser_at (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps))).
Definition ptrans_staleeA (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbeA PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
                (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.

Definition no_args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> Prop := fun _ _ _ _ _ _ _ => True.
Definition std_args (R : bvmap 5 word) (M : mem) (P V E : Z) (ps : pstate) : Prop := a0 R P /\ a1 R V /\ a2 R E.
Definition cur_args (R : bvmap 5 word) (M : mem) (P V E : Z) (ps : pstate) : Prop :=
  a0 R P /\ a2 R V /\ a3 R E /\ exists p e, PML.ps_win ps = Some (p, e) /\ a1 R p.
Definition win_exhausted (ps : pstate) : Prop := match PML.ps_win ps with None => True | Some (p, e) => p = e end.
Definition consumed (ps ps' : pstate) : Prop :=
  match PML.ps_win ps, PML.ps_win ps' with Some (p, e), Some (p', e') => e' = e /\ p < p' <= e | _, _ => False end.
Definition not_retreated (ps ps' : pstate) : Prop :=
  match PML.ps_win ps, PML.ps_win ps' with Some (p, e), Some (p', e') => e' = e /\ p <= p' <= e | None, None => True | _, _ => False end.

(* [comment removed for export] *)
Definition set_ec_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (E code sp r : Z) (g : PML.ls_state),
    cps_asan pc r sp SETEC_SCR LB FF LK cr A 0
      (fun R M => a0 R E /\ a1 R code /\ 1 <= code <= 31 /\ L5.defined M E 16 /\ fobj M FF E 16 /\ stksh M sp SETEC_SCR /\ ls_ok g M /\ g <> PML.LS0)
      (fun R M R' M' LB' cr' LBk W => ec_at M' E code /\ ls_ok PML.LS2 M' /\ a0 R' E /\ LB' = LB /\ cr' = cr /\ LBk = LB /\
                                      W = [(E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)]).

(* [comment removed for export] *)
Definition vstub_specA (pc : Z) : Prop :=          (* [comment removed for export] *)
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r : Z),
    cps_asan pc r sp 0 LB FF LK cr A 0 (fun R M => True) (fun R M R' M' LB' cr' LBk W => a0 R' 1 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).
Definition errh_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (t v sp r : Z),
    cps_asan pc r sp 16 LB FF LK cr A 0
      (fun R M => a1 R t /\ ainfr FF t 8 /\ t mod 8 = 0 /\ byte_at M (S t) 4 /\ u32 M t v /\ 0 <= v < 2 ^ 31)
      (fun R M R' M' LB' cr' LBk W => a0 R' (if Z.eqb v 24 then 1 else 0) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
Definition parent_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P b cap x sp r : Z) (rest : list Z),
    cps_asan pc r sp PARENT_SCR LB FF LK cr A 2
      (fun R M => a0 R P /\ sp mod 32 = 0 /\ vec_ok M LB FF (P + 248) b (Z.of_nat (length rest) + 1) cap /\ L5.bytes_at (hl_segs L) M b (rest ++ [x]) /\ 0 <= x < 256)
      (fun R M R' M' LB' cr' LBk W => a0 R' x /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
Definition skip_space_specA (pc : Z) : Prop :=
  ptransA pc PF_SCR 4 false (fun R M LBo P V E ps => a0 R P /\ a1 R (P + 200) /\ PML.ws_ok ps /\
                                (* [comment removed for export] *)
                                (if PML.ps_more ps then PML.is_expect (PML.ps_st ps) else PML.ps_st ps = PML.ST_DONE) /\
                                exists p e b, PML.ps_win ps = Some (p, e) /\ p < e /\ u8 M p b /\ In b [9; 10; 13; 32])
         (fun ps ps' code R' => code = 0 /\ consumed ps ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ws_ok ps' /\
                                (PML.ps_st ps' = PML.ps_st ps \/ (PML.ps_st ps' = PML.ST_CR /\ win_exhausted ps')) /\ PML.ps_level ps' = PML.ps_level ps).

(* [comment removed for export] *)
Definition begin_container_specA (pc kind st' : Z) : Prop :=
  ptransA pc PF_SCR 5 true (fun R M LBo P V E ps => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_level ps' = PML.ps_level ps + 1 /\ PML.ps_st ps' = st' /\ PML.ps_more ps' = true /\ PML.ps_stack ps' = PML.ps_stack ps ++ [kind] /\ PML.ps_win ps' = PML.ps_win ps)
            \/ (code = 5 /\ PML.ps_level ps = 1024 /\ PML.ps_win ps' = PML.ps_win ps)).
Definition begin_object_specA (pc : Z) := begin_container_specA pc PML.ST_OBJECT PML.ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_specA (pc : Z) := begin_container_specA pc PML.ST_ARRAY PML.ST_EXPECT_VALUE_OR_END.

(* [comment removed for export] *)
Definition end_container_specA (pc kind : Z) : Prop :=
  ptransA pc PF_SCR 3 true (fun R M LBo P V E ps => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_level ps' = PML.ps_level ps - 1 /\ PML.ps_more ps' = true /\ (exists rest, PML.ps_stack ps = rest ++ [kind] /\ PML.ps_stack ps' = rest) /\
             PML.ps_st ps' = (if Z.eqb (PML.ps_level ps') 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\ PML.ps_win ps' = PML.ps_win ps)
            \/ (In code [20; 21; 22; 23] /\ PML.ps_win ps' = PML.ps_win ps)).
Definition end_object_specA (pc : Z) := end_container_specA pc PML.ST_OBJECT.
Definition end_array_specA (pc : Z) := end_container_specA pc PML.ST_ARRAY.

(* [comment removed for export] *)
Definition begin_member_specA (pc : Z) : Prop :=
  ptransA pc PF_SCR 3 true (fun R M LBo P V E ps => a0 R P /\ a1 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_EXPECT_COMMA_OR_END)
         (fun ps ps' code R' => code = 0 /\ PML.ps_more ps' = true /\ In (PML.ps_st ps') [PML.ST_EXPECT_MEMBER_NAME; PML.ST_EXPECT_VALUE] /\
                                PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps).
Definition after_value_specA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptrans_stalekA pc AFTERV_SCR 3 true (fun R M LBo P V E ps => a0 R P /\ a1 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER)
         (fun ps ps' code R' => code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps).

(* [comment removed for export] *)
Definition literal_rel (ps ps' : pstate) (code : Z) : Prop :=
  (code = 0 /\ consumed ps ps' /\ PML.ps_more ps' = true /\ PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps)
  \/ (code = 11 /\ PML.ps_win ps' = PML.ps_win ps).          (* [comment removed for export] *)
Definition parse_true_specA (pc : Z) : Prop :=
  ptrans_curA pc PF_SCR 2 true (fun R M LBo P V E ps => cur_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p)).      (* [comment removed for export] *)
Definition parse_false_specA (pc : Z) : Prop :=
  ptrans_curA pc PF_SCR 2 true (fun R M LBo P V E ps => cur_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p)).      (* [comment removed for export] *)
Definition parse_null_specA (pc : Z) : Prop :=
  ptransA pc PF_SCR 2 true (fun R M LBo P V E ps => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code).

(* [comment removed for export] *)
Definition text_inA (M : mem) (LB : list (Z * Z)) (s len : Z) : Prop :=
  exists b n, In (b, n) LB /\ n mod 8 = 0 /\ b <= s /\ s + len <= b + n /\ shadow_zero M b (n / 8).
(* [comment removed for export] *)
Definition validate_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s len sp r : Z),
    cps_asan pc r sp 128 LB FF LK cr A 0      (* [comment removed for export] *)
      (fun R M => a0 R s /\ a1 R len /\ 0 <= len < 2 ^ 27 /\ L5.defined M s len /\ PMLA.img_ro IC M /\ text_inA M LB s len)
      (fun R M R' M' LB' cr' LBk W => (exists q c, a0 R' q /\ getr R' 11%bv = Z_to_bv 64 c /\ s <= q <= s + len /\ 0 <= c <= 6) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
Definition end_string_value_specA (pc : Z) : Prop :=
  ptrans_staleA pc ESV_SCR 3 true
         (fun R M LBo P V E ps => a0 R P /\ a3 R V /\ a4 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING /\
                              exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                            (* [comment removed for export] *)
                                            text_inA M (PML.ps_blocks ps ++ LBo) s len)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps /\
             In (PML.ps_st ps') [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).

(* [comment removed for export] *)
Definition parse_string_specA (pc : Z) : Prop :=
  ptrans_curA pc PF_SCR 4 true (fun R M LBo P V E ps => cur_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING)
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ consumed ps ps' \/ win_exhausted ps) /\
                                (code = 0 -> PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps)).

(* [comment removed for export] *)
Definition dec_u64_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s len vp sp r : Z),
    cps_asan pc r sp 64 LB FF LK cr A 0
      (fun R M => PMLA.img_ro IC M (* [comment removed for export] *) /\ a0 R s /\ a1 R len /\ a2 R vp /\ 0 <= len < 2 ^ 27 /\ L5.defined M s len /\
                  text_inA M LB s len /\ L5.defined M vp 8 /\ acobj FF sp vp 8 /\ vp mod 8 = 0 /\ shadow_zero M vp 1)
      (fun R M R' M' LB' cr' LBk W => (exists q c, a0 R' q /\ getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 22; 34]) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(vp, 8)]).

(* [comment removed for export] *)
Definition decstr_to_double_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s dp sp r : Z) (txt : list Z),
    cps_asan pc r sp DECSTR_SCR LB FF LK cr A 2
      (fun R M => a0 R s /\ a1 R (Z.of_nat (length txt)) /\ a2 R dp /\ sp mod 32 = 0 /\ PMLA.img_ro IC M /\ stksh M sp DECSTR_SCR /\
                  L5.bytes_at (hl_segs L) M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ PML.num_final txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\
                  (exists b, In b LB /\ fst b <= s /\ s + Z.of_nat (length txt) + 1 <= fst b + snd b) /\
                  L5.defined M dp 8 /\ acobj FF sp dp 8 /\ dp mod 8 = 0 /\ shadow_zero M dp 1)     (* [comment removed for export] *)
      (fun R M R' M' LB' cr' LBk W => a0 R' (s + Z.of_nat (length txt)) /\ (exists c, getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 34]) /\
                                      LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(dp, 8); (hl_tp L - 164, 4)]).

(* [comment removed for export] *)
Definition end_number_specA (pc : Z) : Prop :=
  ptrans_staleA pc ENDNUM_SCR 4 true (fun R M LBo P V E ps => std_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps))
         (fun ps ps' code R' => (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                 PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) \/ code = 19).
Definition end_integer_value_specA (pc : Z) := end_number_specA pc.
Definition end_fraction_value_specA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptrans_staleeA pc ENDNUM_SCR 4 true (fun R M LBo P V E ps => std_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps))
         (fun ps ps' code R' => (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                 PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) \/ code = 19).

(* [comment removed for export] *)
Definition parse_number_specA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptrans_cureA pc PF_SCR 5 true (fun R M LBo P V E ps => cur_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER)
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code = 0 -> PML.ps_level ps' = PML.ps_level ps /\ PML.ps_more ps' = true /\ (PML.ps_st ps' = PML.ST_NUMBER -> win_exhausted ps') /\
                                             In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END])).

(* [comment removed for export] *)
Definition parse_some_specA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptranseA pc PSOME_SCR 6 true (fun R M LBo P V E ps => std_args R M P V E ps /\ PML.ps_more ps = true (* [comment removed for export] *))
         (fun ps ps' code R' =>
            (code <> 0 \/ PML.ps_more ps' = false \/ win_exhausted ps') /\
            (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
            (win_exhausted ps -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR]) /\
            (code = 0 -> PML.ws_ok ps')).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition skip_whitespace_specA (pc : Z) : Prop :=
  ptransA pc SKIPWS_SCR 4 true (fun R M LBo P V E ps => a0 R P /\ PML.ws_ok ps /\ (PML.ps_more ps = true -> win_exhausted ps))      (* [comment removed for export] *)
         (fun ps ps' code R' => code = 0 /\ not_retreated ps ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ws_ok ps').
Definition parser_check_done_specA (pc : Z) : Prop :=
  ptransA pc PF_SCR 2 true (fun R M LBo P V E ps => a0 R P /\ a1 R E)      (* [comment removed for export] *)
         (fun ps ps' code R' => (code = 0 /\ win_exhausted ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ps_st ps' = PML.ps_st ps /\ PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps) \/ code = 4).

(* [comment removed for export] *)
Definition TCE_SCR : Z := 96 + SETEC_SCR.
Definition tce_code (cls : Z) : Z := if cls =? 1 then 26 else if cls =? 2 then 25 else if cls =? 3 then 29 else if cls =? 4 then 28 else 27.
Definition translate_conv_errc_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P E cls sp r : Z) (g : PML.ls_state),
    cps_asan pc r sp TCE_SCR LB FF LK cr A 2
      (fun R M => a0 R P /\ a1 R cls /\ a2 R E /\ 1 <= cls <= 6 /\ sp mod 32 = 0 /\ stksh M sp TCE_SCR /\ u64 M (P + 96) (PMLA.VT_FUNC IC) /\ u64 M (P + 128) (P + 96) /\
                  fobj M FF P 272 /\ fobj M FF E 16 /\ PMLA.apart P 272 E 16 /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0)
      (fun R M R' M' LB' cr' LBk W => ec_at M' E (tce_code cls) /\ u8 M' (P + 211) 0 /\ ls_ok PML.LS2 M' /\ LB' = LB /\ cr' = cr /\ LBk = LB /\
                                      W = [(P + 211, 1); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)]).
(* [comment removed for export] *)
Definition ATC_SCR : Z := 96 + SETEC_SCR.
Definition is_hex (c : Z) : Prop := 48 <= c <= 57 \/ 97 <= c <= 102 \/ 65 <= c <= 70.
Definition append_to_codepoint_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (P E cp c sp r : Z) (g : PML.ls_state),
    cps_asan pc r sp ATC_SCR LB FF LK cr A 2
      (fun R M => a0 R P /\ a1 R cp /\ a2 R c /\ a3 R E /\ 0 <= cp < 2 ^ 64 (* [comment removed for export] *) /\ 0 <= c <= 255 /\ sp mod 32 = 0 /\ stksh M sp ATC_SCR /\
                  u64 M (P + 96) (PMLA.VT_FUNC IC) /\ u64 M (P + 128) (P + 96) /\ u8 M (P + 211) 1 /\ fobj M FF P 272 /\ fobj M FF E 16 /\ PMLA.apart P 272 E 16 /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0)
      (fun R M R' M' LB' cr' LBk W => (exists v, a0 R' v) /\
                                      ((is_hex c /\ ec_at M' E 0 /\ u8 M' (P + 211) 1 /\ ls_ok g M') \/ (~ is_hex c /\ ec_at M' E 17 /\ u8 M' (P + 211) 0 /\ ls_ok PML.LS2 M')) /\
                                      LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(P + 211, 1); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES)]).
(* [comment removed for export] *)
Definition bufcredA (cr : credit) (cap kx bx : Z) : Prop :=
  cap <= 2 ^ 27 /\ 0 <= kx /\ 0 <= bx /\
  Z.log2 (2 ^ 27 / cap) * hl_k_per_malloc L + kx <= fst cr /\
  hl_b_lin L * (2 ^ 28 - 2 * cap) + Z.log2 (2 ^ 27 / cap) * hl_b_overhead L + bx <= snd cr.
Definition convert_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o cap p cpa cp sp r kx bx : Z) (s : list Z),
    cps_asan pc r sp CONVERT_SCR LB FF LK cr A 0
      (fun R M => a0 R cpa /\ a1 R 1 /\ a2 R o /\ a3 R 0 /\
                  u32 M cpa cp /\ 0 <= cp < 2 ^ 32 /\ ainfr FF cpa 4 /\ ((cpa mod 8 = 0 /\ byte_at M (S cpa) 4) \/ byte_at M (S cpa) 0) /\
                  str_at M o (PML.SLong cap p s) /\ 24 <= cap /\ In (p, cap) LB /\ shadow_blk M p cap /\ fobj M FF o 24 /\
                  stksh M sp CONVERT_SCR /\ Z.of_nat (length s) + 4 < 2 ^ 26 /\ bufcredA cr cap kx bx)
      (fun R M R' M' LB' cr' LBk W => exists cap' p' s',
          str_at M' o (PML.SLong cap' p' s') /\ shadow_blk M' p' cap' /\ cap <= cap' /\
          Z.of_nat (length s) <= Z.of_nat (length s') <= Z.of_nat (length s) + 4 /\
          LB' = (p', cap') :: lb_remove p LB /\ LBk = lb_remove p LB /\ W = [(o, 24)] /\ bufcredA cr' cap' kx bx).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition isrc_at := PMLA.isrc_at (hl_segs L) IC.
Definition source_at := PMLA.source_at (hl_segs L) IC.
Definition reader_at := PMLA.reader_at (hl_segs L) IC.
Definition reader_preA (M : mem) (LBo : list (Z * Z)) (FF : list fframe) (Rr IS V E ch : Z) (rep : PML.srep) (gp rdst : Z) (bof : bool) (ps : pstate) : Prop :=
  reader_at M Rr IS V ch bof ps /\ PML.wf_ps ps /\ parser_sh M ps /\ isrc_at M IS rep gp rdst /\ PMLA.srep_sh M rep /\ vis_at M V /\ ec_at M E 0 /\
  In (ch, 16384) LBo /\ shadow_blk M ch 16384 /\ (forall b, In b (PML.srep_blocks rep) -> In b LBo) /\
  fobj M FF Rr 592 /\ fobj M FF IS 272 /\ fobj M FF V 8 /\ fobj M FF E 16 /\
  PMLA.apart Rr 592 IS 272 /\ PMLA.apart Rr 592 V 8 /\ PMLA.apart Rr 592 E 16 /\ PMLA.apart IS 272 V 8 /\ PMLA.apart IS 272 E 16 /\ PMLA.apart V 8 E 16.
Definition ps_init (sb bptr : Z) : pstate := PML.PS PML.ST_START 0 0 true false 0 [PML.ST_ROOT] sb 66 264 bptr [] None.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r Rr IS V E ch gp sb bptr kx bx : Z) (rep : PML.srep) (g : PML.ls_state),
    let ps := ps_init sb bptr in
    cps_asan pc r sp READ_SCR (PML.ps_blocks ps ++ LBo) FF LK cr A 6
      (fun R M => a0 R Rr /\ a1 R E /\ stksh M sp READ_SCR /\
                  reader_preA M LBo FF Rr IS V E ch rep gp 0 true ps /\ gp = PML.srep_data (IS + 80) rep /\
                  (forall b, In b (PML.srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\ ls_ok g M /\ g <> PML.LS0 /\ PMLA.pcredit_xA L cr ps kx bx /\
                  sp mod 32 = 0 (* [comment removed for export] *))
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : PML.ls_state),
          source_at M' Rr ch /\ parser_at M' (Rr + 320) ps' /\ parser_sh M' ps' /\ isrc_at M' IS rep gp' rdst' /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          LB' = PML.ps_blocks ps' ++ LBo /\ LBk = lb_remove ch LBo /\ PMLA.pcredit_xA L cr' ps' kx bx /\ PML.wf_ps ps' /\
          W = [(Rr, 592); (IS, 272); (E, 16); (PMLA.ERRCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)]).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gloc_done (M : mem) : Prop := u8 M (PMLA.GLOC_GUARD IC) 1 /\ u64 M (PMLA.GLOC_PTR IC) (PMLA.CLASSIC_IMP IC).
(* [comment removed for export] *)
Definition locale_ctor_later_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    cps_asan pc r sp 64 LB FF LK cr A 0
      (fun R M => a0 R o /\ gloc_done M (* [comment removed for export] *) /\ PMLA.img_ro IC M /\ acobj FF sp o 8 /\ o mod 8 = 0 /\ L5.defined M o 8)
      (fun R M R' M' LB' cr' LBk W => u64 M' o (PMLA.CLASSIC_IMP IC) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(o, 8)]).
(* [comment removed for export] *)
Definition foot_ranges : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) (PMLA.FOOT IC).
Definition locale_ctor_first_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    cps_asan pc r sp ISLAND_SCR LB FF LK cr A 0
      (fun R M => a0 R o /\ ls_ok PML.LS0 M /\ acobj FF sp o 8 /\ o mod 8 = 0 /\ L5.defined M o 8 /\ stksh M sp ISLAND_SCR)
      (fun R M R' M' LB' cr' LBk W => u64 M' o (PMLA.CLASSIC_IMP IC) /\ u8 M' (PMLA.GLOC_GUARD IC) 1 /\ u64 M' (PMLA.GLOC_PTR IC) (PMLA.CLASSIC_IMP IC) /\
                        PMLA.errcat_guard (hl_segs L) IC M' 0 /\ PMLA.atexit_ok (hl_segs L) IC M' PML.LS0 /\ PMLA.img_ro IC M' /\
                        u8 M' (PMLA.SYSCAT_GUARD IC) 0 /\ u8 M' (PMLA.SYSCAT_GUARD IC + 1) 0 /\
                        LB' = LB /\ cr' = cr /\ LBk = LB /\ W = (o, 8) :: foot_ranges).
(* [comment removed for export] *)
Definition locale_dtor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r : Z),
    cps_asan pc r sp 0 LB FF LK cr A 0
      (fun R M => a0 R o /\ 0 <= o < 2 ^ 62 /\ u64 M o (PMLA.CLASSIC_IMP IC) /\ acobj FF sp o 8)
      (fun R M R' M' LB' cr' LBk W => LB' = LB /\ cr' = cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
Definition strinit_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o src sp r : Z) (txt : list Z),
    cps_asan pc r sp (64 + OPNEW_SCR) LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R src /\ a2 R (Z.of_nat (length txt)) /\ Z.of_nat (length txt) < 2 ^ 26 /\ stksh M sp (64 + OPNEW_SCR) /\
                  L5.bytes_at (hl_segs L) M src txt /\ L5.defined M src (Z.of_nat (length txt)) /\ aacc M src (Z.of_nat (length txt)) /\ fobj M FF o 24 /\ L5.defined M o 24 /\
                  (txt = [] \/ exists b, In b LB /\ fst b <= src /\ src + Z.of_nat (length txt) <= fst b + snd b) /\
                  ((23 <= length txt)%nat -> acredit_ok L cr (PML.str_cap (Z.of_nat (length txt)))))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\
          (((length txt <= 22)%nat /\ str_at_w M' o (PML.SShort txt) /\ LB' = LB /\ cr' = cr)
        \/ ((23 <= length txt)%nat /\ exists p, let cap := PML.str_cap (Z.of_nat (length txt)) in
             str_at_w M' o (PML.SLong cap p txt) /\ afresh LB FF M' p cap /\ LB' = (p, cap) :: LB /\ cr' = adebit L cr cap))).

(* [comment removed for export] *)
Definition statics_mid (M : mem) : Prop :=
  PMLA.img_ro IC M /\ gloc_done M /\ ((u8 M (PMLA.SYSCAT_GUARD IC) 0 /\ u8 M (PMLA.SYSCAT_GUARD IC + 1) 0) \/ u8 M (PMLA.SYSCAT_GUARD IC) 1) /\
  ((PMLA.errcat_guard (hl_segs L) IC M 0 /\ PMLA.atexit_ok (hl_segs L) IC M PML.LS1) \/ (PMLA.errcat_guard (hl_segs L) IC M 1 /\ PMLA.atexit_ok (hl_segs L) IC M PML.LS2)).

(* [comment removed for export] *)
Definition iss_ctor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (IS so sp r : Z) (srep0 : PML.srep),
    cps_asan pc r sp ISS_SCR LB FF LK cr A 0
      (fun R M => a0 R IS /\ a1 R so /\ a2 R 8 /\ stksh M sp ISS_SCR /\
                  str_at_w M so srep0 /\ PMLA.srep_sh M srep0 /\ (forall b, In b (PML.srep_blocks srep0) -> In b LB) /\ Z.of_nat (length (PML.srep_chars srep0)) < 2 ^ 26 /\
                  fobj M FF IS 272 /\ fobj M FF so 24 /\ PMLA.apart IS 272 so 24 /\ L5.defined M IS 272 /\ L5.defined M so 24 (* [comment removed for export] *) /\
                  (ls_ok PML.LS0 M \/ statics_mid M) /\
                  acredit_ok L cr (PML.copy_cap (Z.of_nat (length (PML.srep_chars srep0)))) /\
                  match srep0 with PML.SShort _ => True | PML.SLong _ _ s => (23 <= length s)%nat end (* [comment removed for export] *))
      (fun R M R' M' LB' cr' LBk W => exists rep,
          PML.srep_chars rep = PML.srep_chars srep0 /\ isrc_at M' IS rep (PML.srep_data (IS + 80) rep) 0 /\ statics_mid M' /\
          LB' = PML.srep_blocks rep ++ LB /\ LBk = LB /\
          (forall b, In b (PML.srep_blocks rep) -> afresh LB FF M' (fst b) (snd b) /\ snd b = PML.copy_cap (Z.of_nat (length (PML.srep_chars srep0))) /\ cr' = adebit L cr (snd b)) /\
          (PML.srep_blocks rep = [] -> cr' = cr) /\
          W = (IS, 272) :: foot_ranges).

(* [comment removed for export] *)
Definition reader_ctor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Rr IS V sp r : Z),
    cps_asan pc r sp RCTOR_SCR LB FF LK cr A 5
      (fun R M => a0 R Rr /\ a1 R IS /\ a2 R V /\ sp mod 32 = 0 /\ stksh M sp RCTOR_SCR /\
                  (exists rep gp, isrc_at M IS rep gp 0) /\ vis_at M V /\ PMLA.img_ro IC M /\ gloc_done M /\
                  fobj M FF Rr 592 /\ fobj M FF IS 272 /\ fobj M FF V 8 /\ PMLA.apart Rr 592 IS 272 /\ PMLA.apart Rr 592 V 8 /\ L5.defined M Rr 592 /\
                  3 * hl_k_per_malloc L <= fst cr /\ hl_b_lin L * (16384 + 264 + 66) + 3 * hl_b_overhead L <= snd cr)
      (fun R M R' M' LB' cr' LBk W => exists ch sb bptr,
          reader_at M' Rr IS V ch true (ps_init sb bptr) /\ parser_sh M' (ps_init sb bptr) /\ shadow_blk M' ch 16384 /\
          LB' = PML.ps_blocks (ps_init sb bptr) ++ (ch, 16384) :: LB /\ LBk = LB /\ W = [(Rr, 592)] /\
          cr' = adebit L (adebit L (adebit L cr 16384) 264) 66).

(* [comment removed for export] *)
Definition source_dtor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Rr ch sp r : Z),
    cps_asan pc r sp SDTOR_SCR LB FF LK cr A 0
      (fun R M => a0 R Rr /\ source_at M Rr ch /\ In (ch, 16384) LB /\ PMLA.img_ro IC M /\ fobj M FF Rr 592 /\ stksh M sp SDTOR_SCR)
      (fun R M R' M' LB' cr' LBk W => LB' = lb_remove ch LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = [(Rr, 592)]).
(* [comment removed for export] *)
Definition parser_dtor_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P : Z) (ps : pstate),
    cps_asan pc r sp PDTOR_SCR (PML.ps_blocks ps ++ LBo) FF LK cr A 0
      (fun R M => a0 R P /\ parser_at M P ps /\ parser_sh M ps /\ PMLA.img_ro IC M /\ fobj M FF P 272 /\ stksh M sp PDTOR_SCR /\ 0 < PML.ps_scap ps <= 4096)
      (fun R M R' M' LB' cr' LBk W => LB' = LBo /\ cr' = cr /\ LBk = LBo /\ W = [(P, 272)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_staticsA : lib_statics := {| LibIface.ls_state := PML.ls_state; LibIface.ls_ok := ls_ok; LibIface.ls_g0 := PML.LS0 |}.
Definition pm_creditA (n : Z) : credit := (28 * hl_k_per_malloc L, hl_b_lin L * (2 * n + 2 ^ 28 + 32768) + 28 * hl_b_overhead L).
Definition LIB_FRAMES : Z := 7.       (* [comment removed for export] *)
Definition pm_layout_okA (Lay : lib_layoutA) : Prop :=
  lla_L Lay = L /\ LIB_SCR <= lla_stack Lay /\ lla_stack Lay mod 16 = 0 /\ lla_foot Lay = PMLA.FOOT IC /\
  lla_junk Lay = [(hl_tp L - 164, hl_tp L - 160)] /\                                          (* [comment removed for export] *)
  (forall k, In k PM_FS_CLASSES -> lla_frames Lay k = LIB_FRAMES /\ lla_leak Lay k = 0) /\    (* [comment removed for export] *)
  (forall n, lla_credit Lay n = pm_creditA n) /\ PMLA.IMG_RO_HI IC <= lla_rw_lo Lay /\
  lla_atexit Lay = PMLA.ATEXIT_TAB IC /\ lla_hs0 Lay = PMLA.HS0 IC /\ lla_need_locks Lay = PMLA.NEED_LOCKS IC /\
  (* [comment removed for export] *)
  (forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ (PMLA.in_foot IC a /\ ~ PMLA.in_tab IC a /\ a <> PMLA.NEED_LOCKS IC) ->
             exists iv, In iv (lla_init_img Lay) /\ fst iv <= a < snd iv) /\
  (* [comment removed for export] *)
  (forall M : mem, (forall a, PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> M (Z_to_bv 64 a) = None) -> cell_is (hl_segs L) M (PMLA.LOCALE_LOCK IC) 4 0).
Definition lib_specA (Lay : lib_layoutA) : Prop := pm_layout_okA Lay -> PmLibIfaceA.lib_call_okA Lay ar SCFG HI pm_staticsA.
(* [comment removed for export] *)
Lemma lib_exit_okA : forall (Lay : lib_layoutA), pm_layout_okA Lay -> PmLibIfaceA.lib_exit_factsA Lay pm_staticsA (PMLA.ls_atexit IC).
Proof.
  intros Lay (HL & _ & _ & _ & _ & _ & _ & _ & HA & HH & HN & _) g M Hok. rewrite HA, HH, HN, HL. exact (PMLA.ls_ok_exit (hl_segs L) IC g M Hok).
Qed.
(* [comment removed for export] *)
Definition atexit_handler_specA (ILX : icpt_layout_x) : Prop := forall a : Z, PmIcptIfaceA.ahandler_spec L ar ILX SCFG HI (PMLA.ATEXIT_HANDLER IC) a.

End SpecsA.
End PMSA.
