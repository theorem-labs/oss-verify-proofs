(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_nia__].

Notation SJ_IMPL_HI := (0xedb90)%Z (only parsing).
Notation PJ_NULSB_VT := (0xd68d8)%Z (only parsing).
Notation PJ_XSPUTN := (0x82530)%Z (only parsing).
Notation PJ_OVERFLOW := (0x3fdcc)%Z (only parsing).
Notation PJ_WIDEN_SLOT := (0xda1c0)%Z (only parsing).
Notation PJ_DO_WIDEN := (0xa9050)%Z (only parsing).
Notation PJ_GOT_VT := (0xdc320)%Z (only parsing).
Notation PJ_SB_VT := (0xd9fe0)%Z (only parsing).
Notation PJ_IOS_VT := (0xda060)%Z (only parsing).
Notation PJ_GOT_CTYPE_ID := (0xdc370)%Z (only parsing).
Notation PJ_CTYPE_ID := (0xee080)%Z (only parsing).
Notation PJ_LOCLOCK := (0x10f8f0)%Z (only parsing).
Notation PJ_RELRO_LO := (0xd6810)%Z (only parsing).
Notation PJ_RELRO_HI := (0xdc478)%Z (only parsing).
Notation PJ_RELRO_SSP := (0xdc448)%Z (only parsing).

Notation EL_EHG := (0xedb98)%Z (only parsing).
Notation EL_UNW := (0xef4b0)%Z (only parsing).
Notation EL_XDATA := (0xdd4a0)%Z (only parsing).
Notation EL_XDATA_V0 := (0xd9b48)%Z (only parsing).
Notation EL_XDATA_V1 := (0x7c284)%Z (only parsing).
Notation EL_HDLR := (0xdd7b8)%Z (only parsing).
Notation EL_HDLR_V0 := (0x5f084)%Z (only parsing).
Notation EL_HDLR_V1 := (0x5f190)%Z (only parsing).
Notation EL_MREPL := (0x10fd38)%Z (only parsing).
Notation EL_TPLOC := (0xef558)%Z (only parsing).
Notation EL_GLOC := (0x10f850)%Z (only parsing).
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition lops : target_ops (M PState) bptr := Target.ops raw_malloc raw_free ps_so set_so_ps.

Definition LX_FUZZ : Z := 0x3c018.

Definition LX_GOT_STDERR : Z := 0xdc2f0.
Definition LX_STDERR_PTR : Z := 0xdc298.
Definition LX_STDERR_FILE : Z := 0xdd850.
Definition LX_EMPTY : Z := 0xedab0.

Definition SJ_STATICS_LO : Z := 0xedae8.
Definition SJ_STATICS_HI : Z := 0xeec78.
Definition SJ_ACTIVE_IMPL : Z := 0xedae8.
Definition SJ_GUARD1 : Z := 0xedaf0.
Definition SJ_GUARD2 : Z := 0xedb18.
Definition SJ_FALLBACK : Z := 0xedb60.
Definition SJ_FALLBACK_VPTR : Z := 0xd6c20.
Definition SJ_STR_NAME : Z := 0x13882.
Definition SJ_STR_DESC : Z := 0x10e56.

Definition SJ_GOT_NOTHROW : Z := 0xdc318.
Definition SJ_NOTHROW_TAG : Z := 0x1ca70.
Definition SJ_IMPL_VT24 : Z := 0xd6c38.
Definition SJ_CREATE_DPI : Z := 0x418f8.
Definition SJ_DPI_VPTR : Z := 0xd6c88.
Definition SJ_DPI_PARSE : Z := 0x5af84.
Definition SJ_DPI_STAGE1 : Z := 0x41a2c.
Definition SJ_DPI_STAGE2 : Z := 0x4370c.
Definition SJ_DPI_STAGE2_NEXT : Z := 0x4eefc.
Definition SJ_DPI_PARSE_STRING : Z := 0x5a848.
Definition SJ_DPI_PARSE_WOBBLY : Z := 0x5ac00.
Definition SJ_DPI_SET_CAPACITY : Z := 0x5b180.
Definition SJ_DPI_SET_MAX_DEPTH : Z := 0x5b250.
Definition SJ_DPI_DTOR : Z := 0x5b318.
Definition SJ_DPI_DTOR_DEL : Z := 0x5b380.

Definition SJ_CLIENT_FRAMES : Z := 327844.
Definition LX_FUZZ_STACK : Z := SJ_CLIENT_FRAMES + 32 + RMALLOC_STACK.

Definition pj_relro (m : mem) : Prop :=
  forall a : Z, (PJ_RELRO_LO <= a < PJ_RELRO_SSP \/ PJ_RELRO_SSP + 8 <= a < PJ_RELRO_HI) -> m (wa a) = None.
Definition pj_consts (m : mem) : Prop :=
  rw_cells usegs m PJ_NULSB_VT [C8 (wz PJ_XSPUTN); C8 (wz PJ_OVERFLOW); C8 (wz 8)]
  /\ rw_cells usegs m PJ_WIDEN_SLOT [C8 (wz PJ_DO_WIDEN)]
  /\ rw_cells usegs m PJ_GOT_VT [C8 (wz PJ_IOS_VT); C8 (wz PJ_SB_VT)]
  /\ rw_cells usegs m PJ_GOT_CTYPE_ID [C8 (wz PJ_CTYPE_ID)]
  /\ rw_cells usegs m PJ_LOCLOCK [C4 (wz 0)]
  /\ pj_relro m.

Definition el_consts (m : mem) : Prop :=
  rw_cells usegs m EL_XDATA [C8 (wz EL_XDATA_V0); C8 (wz EL_XDATA_V1)]
  /\ rw_cells usegs m EL_HDLR [C8 (wz EL_HDLR_V0); C8 (wz EL_HDLR_V1)]
  /\ rw_cells usegs m EL_MREPL [C4 (wz 0); C4 (wz 0)]
  /\ rw_cells usegs m EL_TPLOC [C8 (wz EL_GLOC)].

Definition lx_statics (m : mem) : Prop :=
  rw_cells usegs m LX_GOT_STDERR [C8 (wz LX_STDERR_PTR)]
  /\ rw_cells usegs m LX_STDERR_PTR [C8 (wz LX_STDERR_FILE)]
  /\ rw_cells usegs m SJ_GOT_NOTHROW [C8 (wz SJ_NOTHROW_TAG)]
  /\ rw_cells usegs m SJ_IMPL_VT24 [C8 (wz SJ_CREATE_DPI)]
  /\ rw_cells usegs m SJ_DPI_VPTR [C8 (wz SJ_DPI_PARSE); C8 (wz SJ_DPI_STAGE1); C8 (wz SJ_DPI_STAGE2); C8 (wz SJ_DPI_STAGE2_NEXT);
                                   C8 (wz SJ_DPI_PARSE_STRING); C8 (wz SJ_DPI_PARSE_WOBBLY); C8 (wz SJ_DPI_SET_CAPACITY);
                                   C8 (wz SJ_DPI_SET_MAX_DEPTH); C8 (wz SJ_DPI_DTOR); C8 (wz SJ_DPI_DTOR_DEL)]
  /\ pj_consts m
  /\ el_consts m.

Notation zeros := MallocRep.zeros (only parsing).
Definition sj_cells (init : bool) : list cell :=
  if init then
    [C8 (wz SJ_FALLBACK);
     C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); CB 6 (zeros 6);
     CB 32 (zeros 32);
     C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); CB 6 (zeros 6);
     CB 64 (zeros 64);
     C8 (wz SJ_FALLBACK_VPTR); C8 (wz SJ_STR_NAME); C8 (wz 8); C8 (wz SJ_STR_DESC); C8 (wz 31); C4 (wz 0);
     CB 4 (zeros 4)]
  else [CB 168 (zeros 168)].

Definition uw_cells (uw : bool) : list cell :=
  if uw then [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  else [CB 8 (zeros 8)].
Definition el_extra (m : mem) : Prop :=
  rw_cells usegs m EL_EHG [C8 (wz 0); C4 (wz 0)] /\ (exists uw : bool, rw_cells usegs m EL_UNW (uw_cells uw)).
Definition sj_statics (m : mem) (init : bool) : Prop := rw_cells usegs m SJ_STATICS_LO (sj_cells init) /\ pj_locale m /\ el_extra m.

Definition LXW_SJ : Z * Z := (SJ_STATICS_LO, SJ_STATICS_HI).
Definition LXW_UNW : Z * Z := (EL_UNW, EL_UNW + 8).
Definition LXW_TP : Z * Z := (EL_TPLOC, EL_TPLOC + 8).

Fixpoint rin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ rin_ivs X' a end.

Definition lx_client (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop :=
  ~ rin_ivs X a /\ (SP <= a \/ in_block LB a \/ (0xd6000 <= a < 0x111000 /\ ~ ralloc_static a)).

Definition lx_pres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> lx_client LB SP X a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma lx_pres_refl : forall LB SP X m, lx_pres LB SP X m m.
Proof. intros LB SP X m a _ _. auto. Qed.

Lemma lx_pres_trans : forall LB SP X m1 m2 m3,
  lx_pres LB SP X m1 m2 -> lx_pres LB SP X m2 m3 -> lx_pres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma lx_pres_weaken : forall LB LB' SP SP' X X' m m',
  lx_pres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
  lx_pres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha [Hx Hc]. apply H; [exact Ha|].
  split; [intros Hx'; apply Hx; apply HX; exact Hx'|].
  destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left| right; right; exact Hc].
  exists b. split; [apply HL; exact Hb|exact Hr].
Qed.

Lemma lx_pres_of_heap_pres : forall LB SP X m m', rheap_pres LB SP m m' -> lx_pres LB SP X m m'.
Proof.
  intros LB SP X m m' H a Ha [_ Hc]. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc| right; right; exact Hc| right; left; exact Hc].
Qed.

Definition payload_ok (m : mem) (LB : list block) (D : Z) (d : list Z) : Prop :=
  bytes_at usegs m D (to_bytes d) /\ Forall (fun c => 0 <= c < 256) d
  /\ 0 < D /\ D + zlength d < 2^63 /\ zlength d < 2^26
  /\ (d = [] \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b).

Definition lx_env (m : mem) (s : PState) (OW LB : list block) (sp tp : word) (B lo : Z) (errv canary : word) : Prop :=
  RHEAP s (OW ++ LB) m /\ lx_statics m /\ (exists init, sj_statics m init) /\ stderr_wfile m /\ ssp_cells m canary
  /\ rauxv_ok m B /\ bv_unsigned sp <= B /\ B < 2^63
  /\ stk usegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
  /\ rw_cells usegs m (errno_addr tp) [C4 errv] /\ tp = wz RATP
  /\ mem_inv usegs m.

Definition lx_post_env (m m' : mem) (s s' : PState) (OW' LB : list block) (sp tp : word) (B lo : Z) (canary : word)
    (X : list (Z * Z)) (fc' : bv 32) : Prop :=
  (exists errv' : word, lx_env m' s' OW' LB sp tp B lo errv' canary)
  /\ frm0 fc'
  /\ lx_pres LB (bv_unsigned sp) X m m'
  /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.

Definition rfuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [LXW_SJ; LXW_UNW; LXW_TP] fc'
    /\ (exists init' : bool, sj_statics m' init')
    /\ r = 0 /\ a0 = wz 0
    /\ payload_ok m' LB D d.

Definition rfuzz_one_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (D : Z) (d : list Z) (init : bool) (lo B : Z) (errv canary : word),
  RHEAP s LB m -> lx_statics m -> sj_statics m init -> stderr_wfile m -> ssp_cells m canary ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^62 ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv usegs m ->
  bv_unsigned sp mod 16 = 0 ->
  payload_ok m LB D d ->
  frm0 fc ->
  a0 = wz D -> a1 = wz (zlength d) ->
  implM usegs (ElModel.fuzz_one lops d) s
        (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz LX_FUZZ) fc None m (seg_rom usegs)).
End WithCeiling0.

