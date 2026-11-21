(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import TSet ZStep ZMem ZCall ZCallL ZArr IDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Definition it_ret   (r : Z * arr * Z * Z * arr) : Z   := fst (fst (fst (fst r))).
Definition it_tbl   (r : Z * arr * Z * Z * arr) : arr := snd (fst (fst (fst r))).
Definition it_table (r : Z * arr * Z * Z * arr) : Z   := snd (fst (fst r)).
Definition it_bits  (r : Z * arr * Z * Z * arr) : Z   := snd (fst r).
Definition it_work  (r : Z * arr * Z * Z * arr) : arr := snd r.

Definition cty (ty : codetype) : Z := match ty with CODES => 0 | LENS => 1 | DISTS => 2 end.

Definition kept_eq (Rb : tree Z) (l : list (positive * Z)) (R' : tree Z) : Prop :=
  zget R' kSP = zget_l Rb l kSP /\ zget R' kGP = zget_l Rb l kGP /\ zget R' kTP = zget_l Rb l kTP /\
  zget R' kS0 = zget_l Rb l kS0 /\ zget R' kS1 = zget_l Rb l kS1 /\ zget R' kS2 = zget_l Rb l kS2 /\
  zget R' kS3 = zget_l Rb l kS3 /\ zget R' kS4 = zget_l Rb l kS4 /\ zget R' kS5 = zget_l Rb l kS5 /\
  zget R' kS6 = zget_l Rb l kS6 /\ zget R' kS7 = zget_l Rb l kS7 /\ zget R' kS8 = zget_l Rb l kS8 /\
  zget R' kS9 = zget_l Rb l kS9 /\ zget R' kS10 = zget_l Rb l kS10 /\ zget R' kS11 = zget_l Rb l kS11.

Definition it_fp (p pb sp FR : Z) : list (Z * Z) :=
  [(sp - FR, FR); (p + o_next, 8); (pb, 4); (p + o_work, 2 * N_WORK); (p + o_codes, 4 * N_CODES)].

Definition itable_spec_at (segs : list Segment) (pc FR : Z) : Prop :=
  forall Rb l M MD T (ty : codetype) (p lens_ofs codes nx bits pb sp ret zc : Z) (lf cf wf : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = cty ty -> zget_l Rb l kA1 = p + o_lens + 2 * lens_ofs -> zget_l Rb l kA2 = codes ->
  zget_l Rb l kA3 = p + o_next -> zget_l Rb l kA4 = pb -> zget_l Rb l kA5 = p + o_work ->
  zget_l Rb l kSP = sp -> zget_l Rb l kRA = ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  (pb = p + o_lenbits \/ pb = p + o_distbits) ->
  p mod 16 = 0 -> 0 < p -> p + STATE_SIZE <= zc -> zc + FR <= sp ->
  DEXT_ADDR + 64 <= zc ->
  sp <= 140737488355328 -> sp mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ DEXT_ADDR + 64 <= p) ->
  mem_wr segs M (sp - FR) FR -> mem_wr segs M p STATE_SIZE ->
  mem_arr 2 segs M (p + o_lens) N_LENS lf -> mem_arr 4 segs M (p + o_codes) N_CODES cf -> mem_arr 2 segs M (p + o_work) N_WORK wf ->
  mem_u64 segs M (p + o_next) (p + o_codes + 4 * nx) -> mem_u32 segs M pb bits ->
  mem_arr 2 segs M LBASE_ADDR 31 (arr_get lbase_a) -> mem_arr 2 segs M LEXT_ADDR 31 (arr_get lext_a) ->
  mem_arr 2 segs M DBASE_ADDR 32 (arr_get dbase_a) -> mem_arr 2 segs M DEXT_ADDR 32 (arr_get dext_a) ->
  (forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) ->
  (forall i, 0 <= i < N_WORK -> 0 <= wf i < 65536) ->
  0 <= lens_ofs -> lens_ofs + codes <= N_LENS -> 0 <= codes -> codes <= 288 ->
  (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 15) ->
  (ty = CODES -> codes <= 19 /\ bits = 7 /\ (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 7)) ->
  (ty = DISTS -> codes <= 32) ->
  1 <= bits -> bits <= 15 -> 0 <= nx -> nx + it_room ty <= N_CODES ->
  (forall R' M' (cf' wf' : Z -> Z),
     let r := inflate_table ty (arr_init N_LENS lf) lens_ofs codes (arr_init N_CODES cf) nx bits (arr_init N_WORK wf) in
     zget R' kA0 = it_ret r ->
     (it_ret r = 0 \/ it_ret r = 1 \/ it_ret r = -1) ->
     (forall i, 0 <= i < N_CODES -> cf' i = arr_get (it_tbl r) i) ->
     (forall i, 0 <= i < N_WORK -> wf' i = arr_get (it_work r) i) ->
     (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
     (forall i, 0 <= i < N_WORK -> 0 <= wf' i < 65536) ->
     mpostL segs M M' (it_fp p pb sp FR) ->
     mem_arr 2 segs M' (p + o_lens) N_LENS lf -> mem_arr 4 segs M' (p + o_codes) N_CODES cf' -> mem_arr 2 segs M' (p + o_work) N_WORK wf' ->
     mem_u64 segs M' (p + o_next) (p + o_codes + 4 * it_table r) -> mem_u32 segs M' pb (it_bits r) ->
     kept_eq Rb l R' ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

Definition if_fp (u p ob osz spi FR : Z) : list (Z * Z) :=
  [(spi - FR, FR); (u, 56); (p + 8, 4); (p + 96, 12); (ob, osz)].

Definition ifast_spec_at (segs : list Segment) (pc FR : Z) : Prop :=
  forall Rb l M MD T (u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd spi ret rhi zc : Z)
         (rdL rdD fin fo fw : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = u -> zget_l Rb l kA1 = out -> zget_l Rb l kSP = spi -> zget_l Rb l kRA = ret ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  zc + FRA <= u -> u + 208 <= 140737488355328 -> spi + 224 <= u -> u - FRA + FR <= spi -> spi mod 16 = 0 -> u mod 16 = 0 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= zc ->
  0 < ob -> 1 <= osz -> osz <= 262144 -> ob + osz <= u -> ZSEP (ob + osz <= u - FRA \/ u + 7 <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) -> ZSEP (p + STATE_SIZE <= q \/ q + n <= p) -> ZSEP (ob + osz <= q \/ q + n <= ob) ->
  (w = 0 \/ (0 < w /\ w + WIN_SIZE <= zc /\ w mod 16 = 0)) ->
  ZSEP (w = 0 \/ (p + STATE_SIZE <= w \/ w + WIN_SIZE <= p)) -> ZSEP (w = 0 \/ (w + WIN_SIZE <= q \/ q + n <= w)) ->
  ZSEP (w = 0 \/ (w + WIN_SIZE <= ob \/ ob + osz <= w)) ->
  0 < la -> la + 4 * na <= zc -> 0 < da -> da + 4 * nd <= zc -> la mod 2 = 0 -> da mod 2 = 0 ->
  ZSEP (la + 4 * na <= ob \/ ob + osz <= la) -> ZSEP (la + 4 * na <= p \/ p + 1384 <= la) ->
  ZSEP (da + 4 * nd <= ob \/ ob + osz <= da) -> ZSEP (da + 4 * nd <= p \/ p + 1384 <= da) ->
  1 <= lb -> lb <= 15 -> 1 <= db -> db <= 15 ->
  tab_ok LENS rdL lb na = true -> tab_ok DISTS rdD db nd = true ->
  0 <= cin -> cin <= n -> 6 <= n - cin -> 0 <= cout -> cout <= osz -> 258 <= osz - cout ->
  0 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits -> bits <= 8 * cin ->
  osz - cout <= out -> out <= osz -> out - (osz - cout) <= cout ->
  0 <= whave -> 0 <= wnext -> (w = 0 -> whave = 0 /\ wnext = 0) -> (w <> 0 -> whave <= WIN_SIZE /\ wnext < WIN_SIZE /\ (whave < WIN_SIZE -> wnext = whave)) ->
  mem_wr segs M (u - FRA) (FRA + 208) -> mem_wr segs M p STATE_SIZE -> mem_wr segs M ob osz -> (w <> 0 -> mem_wr segs M w WIN_SIZE) ->
  mem_u64 segs M (u) (q + cin) -> mem_u32 segs M (u + 8) (n - cin) ->
  mem_u64 segs M (u + 24) (ob + cout) -> mem_u32 segs M (u + 32) (osz - cout) -> mem_u64 segs M (u + 56) p ->
  mem_u32 segs M (p + 72) (if w =? 0 then 0 else WIN_SIZE) -> mem_u32 segs M (p + 76) whave -> mem_u32 segs M (p + 80) wnext ->
  mem_u64 segs M (p + 88) w -> mem_u64 segs M (p + 96) hold -> mem_u32 segs M (p + 104) bits -> mem_u32 segs M (p + 8) LEN ->
  mem_u64 segs M (p + 120) la -> mem_u64 segs M (p + 128) da -> mem_u32 segs M (p + 136) lb -> mem_u32 segs M (p + 140) db ->
  mem_u32 segs M (p + 7160) 1 ->
  mem_arr 4 segs M la na rdL -> mem_arr 4 segs M da nd rdD ->
  mem_arr 1 segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 1 segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  (w <> 0 -> mem_arr 1 segs M w WIN_SIZE fw) -> (forall i, 0 <= i < WIN_SIZE -> 0 <= fw i < 256) ->
  (forall R' M' (cin' cout' hold' bits' mode' : Z) (fo' : Z -> Z),
     0 <= cin' -> cin' <= n -> cout <= cout' -> cout' <= osz ->
     0 <= bits' -> bits' <= 7 -> 0 <= hold' -> hold' < 2 ^ bits' -> bits' <= 8 * cin' ->
     8 * (n - cin') + bits' + (osz - cout') < 8 * (n - cin) + bits + (osz - cout) ->
     8 * (n - cin') + bits' <= 8 * (n - cin) + bits ->
     (mode' = LEN \/ mode' = TYPE \/ mode' = BAD) ->
     mpostL segs M M' (if_fp u p ob osz spi FR) ->
     mem_u64 segs M' (u) (q + cin') -> mem_u32 segs M' (u + 8) (n - cin') ->
     mem_u64 segs M' (u + 24) (ob + cout') -> mem_u32 segs M' (u + 32) (osz - cout') ->
     mem_u64 segs M' (p + 96) hold' -> mem_u32 segs M' (p + 104) bits' -> mem_u32 segs M' (p + 8) mode' ->
     mem_arr 1 segs M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     kept_eq Rb l R' ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
