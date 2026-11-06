From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes EntC1_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet pj_parse_c parse_noting_c check_no_overread_c check_as_written_c
  check_reject_clean_starved_c check_round_trip_c pj_free_c EntryDefs EntrySR EntBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The stages of LLVMFuzzerTestOneInput on the #102 ubsan pin (fuzz_preset.c:800-836; twin 27566683952ebd54...,
   FUNC 0x13718): the CF twins of lib/Prog/EntStg.v (cold/h-rw-pre-4-rw102-ent f3c1596d9c63), each pc + 0xf0.
   Each stage is a callee entry with the entry's return address in ra; it states the entry's frame (ent_inv), the
   registers the code reads after the call, and out_of_memory() = 0 (ent_flags) where a later step reads it.
   Frame: S = spZ regs0; sp = S - 112; the doc at S - 112; ra, s0-s5 saved at S - 8 .. S - 56. The registers the
   prologue does not save (gp, tp, s6-s11) stay as at the entry (ent_rk).
   Registers: s0 = size, s1 = data, s2 = live (= 0), s3 = count before the reading, then took; s4 = rc; s5 =
   GL_OWN_RAN_OUT + 0x4f8 until 0x137b8, then the count after the reading. *)
Definition ent_rk (regs0 regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 22 = getr regs0 22 /\ getr regs 23 = getr regs0 23 /\ getr regs 24 = getr regs0 24 /\
  getr regs 25 = getr regs0 25 /\ getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27.

Definition ent_cnow (x : list byte) (E1 E2 E3 : list (Z * Z)) : Prop :=
  cno_dl (ent_T x) E1 /\ cno_dl (ent_T x) E2 /\ cno_dl (ent_T x) E3.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Definition ent_tree (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem : word -> option byte)
    (Lam : list (Z * Z)) (x : list byte) (t : jv) (D : list (Z * Z)) : Prop :=
  Permutation Lam D /\ pj_node segs mem (lin Lam) (spZ regs0 - 112) t D /\ ent_tree_dl x D /\ new_blks L0 A0 D.

(* check_no_overread (0x13868) called at 0x1376c *)
Definition stg_cno_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md peak,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md [] peak cnt0 b0 ->
  getr regs 1 = Z_to_bv 64 0x13770 -> ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8) -> ent_flags segs mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

(* parse_noting (0x13a38) called at 0x13794, after live = 0, count = cnt0 + 3 took and fuzz_alloc_peak_reset *)
Definition stg_pjp_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md E1 E2 E3,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md [] 0 (cnt0 + 3 * ent_took pl)
    (ent_b1 F b0 pl E1 E2 E3) ->
  getr regs 1 = Z_to_bv 64 0x13798 -> ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 (spZ regs0 - 112) ->
  getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl) ->
  getr regs 21 = Z_to_bv 64 (GL_OWN_RAN_OUT + 0x4f8) -> ent_flags segs mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 PARSE_NOTING) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

(* check_as_written (0x13ad4) called at 0x137d4: rc in a2 and s4, count before in s3, count after in s5 *)
Definition stg_caw_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md Lam peak E1 E2 E3 D Dp,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak (ent_c3 cnt0 pl)
    (ent_b2 F b0 pl E1 E2 E3 Dp) ->
  getr regs 1 = Z_to_bv 64 0x137d8 -> ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 (spZ regs0 - 112) ->
  getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 (cnt0 + 3 * ent_took pl) ->
  getr regs 21 = Z_to_bv 64 (ent_c3 cnt0 pl) -> ent_flags segs mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 -> ent_tree_dl pl D ->
  match json_read jr_strtod (zb pl) with
  | Some t =>
      getr regs 12 = Z_to_bv 64 0 /\ getr regs 20 = Z_to_bv 64 0 /\ Dp = [] /\
      ent_tree L0 A0 regs0 mem Lam pl t D
  | None =>
      getr regs 12 = Z_to_bv 64 (-1) /\ getr regs 20 = Z_to_bv 64 (-1) /\ Lam = [] /\ Permutation D Dp /\
      pj_zero segs mem (spZ regs0 - 112)
  end ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

(* check_reject_clean_starved (0x13c3c) called at 0x13834 with doc = NULL (rc != 0) *)
Definition stg_crs0_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md peak E1 E2 E3 D Dp,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md [] peak (ent_c3 cnt0 pl)
    (ent_b3 F b0 pl E1 E2 E3 Dp) ->
  getr regs 1 = Z_to_bv 64 0x13838 -> ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 (ent_took pl) -> getr regs 13 = Z_to_bv 64 0 -> ent_flags segs mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 ->
  json_read jr_strtod (zb pl) = None -> Permutation D Dp -> ent_tree_dl pl D ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CRCS) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

(* check_round_trip (0x1408c) called at 0x13848, after read_members; took in s3 *)
Definition stg_crt_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md Lam peak E1 E2 E3 t D,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak (ent_c3 cnt0 pl)
    (ent_b3 F b0 pl E1 E2 E3 []) ->
  getr regs 1 = Z_to_bv 64 0x1384c -> ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs 19 = Z_to_bv 64 (ent_took pl) -> ent_flags segs mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 ->
  json_read jr_strtod (zb pl) = Some t -> ent_tree L0 A0 regs0 mem Lam pl t D ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

(* check_reject_clean_starved (0x13c3c) called at 0x13860 with doc = &doc (check_round_trip returned 0) *)
Definition stg_crs1_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md Lam peak E1 E2 E3 t D cset b4,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak (ent_c4 cnt0 pl t cset) b4 ->
  getr regs 1 = Z_to_bv 64 0x13864 -> ent_rk regs0 regs ->
  getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 (ent_took pl) -> getr regs 13 = Z_to_bv 64 (spZ regs0 - 112) -> ent_flags segs mem ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 ->
  json_read jr_strtod (zb pl) = Some t -> ent_tree L0 A0 regs0 mem Lam pl t D ->
  0 <= cset <= 3 -> crt_fin F (ent_b3 F b0 pl E1 E2 E3 []) (ent_c3 cnt0 pl) t cset b4 ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 CRCS) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

(* pj_free (0x16340) called at 0x137e0 on the rc = 0 path after check_reject_clean_starved *)
Definition stg_pjf_st : Prop :=
  forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A regs mem md Lam peak E1 E2 E3 t D cset b4 trs Ds,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak
    (ent_c4 cnt0 pl t cset + crcs_growth (zb pl) (ent_took pl) 1 t)
    (ent_b5 F b4 (ent_c4 cnt0 pl t cset) pl t trs Ds) ->
  getr regs 1 = Z_to_bv 64 0x137e4 -> ent_rk regs0 regs ->
  getr regs 10 = Z_to_bv 64 (spZ regs0 - 112) ->
  0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  entry_rooms F b0 cnt0 pl -> ent_n pl <= 0x300000 -> ent_cnow pl E1 E2 E3 ->
  json_read jr_strtod (zb pl) = Some t -> ent_tree L0 A0 regs0 mem Lam pl t D ->
  0 <= cset <= 3 -> crt_fin F (ent_b3 F b0 pl E1 E2 E3 []) (ent_c3 cnt0 pl) t cset b4 ->
  (ent_took pl <> 0 -> crs_parse_left (ent_c4 cnt0 pl t cset) (zb pl) (ent_took pl) trs Ds) ->
  SR segs (mkCfg (@mkst fx1 regs (Z_to_bv 64 PJ_FREE) mem (seg_rom segs)) md)
    (ent_sr_post B API F stk j L0 A0 regs0 mem0 md0 ra p n pl cnt0 b0).

End S.
