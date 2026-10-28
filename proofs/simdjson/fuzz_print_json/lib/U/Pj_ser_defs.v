(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit Pj_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition PJ_NE_TAB : Z := 0x13554.
Definition PJ_ESC_TAB : Z := 0x13654.
Definition PJ_STR_FALSE : Z := 0x10298.
Definition PJ_STR_TRUE : Z := 0x117fc.
Definition PJ_STR_NULL : Z := 0x10e18.
Definition PJ_LIT_BS : Z := 0x1102f.
Definition PJ_LIT_QU : Z := 0x119df.
Definition PJ_ITOA_MAGIC : Z := 0x13460.

Definition PJ_TAPE_REF : Z := 0x3d090.
Definition PJ_ITOA_S : Z := 0x3d3a8.
Definition PJ_ITOA_U : Z := 0x3d484.
Definition PJ_MEMCPY : Z := 0xcfe78.
Definition PJ_SER_TRAP : Z := 0x3eef0.

Definition PJ_TMASK : Z := 18374686479671623680.
Definition PJ_PMASK : Z := 72057594037927935.
Definition PJ_RBK56 : Z := 6701356245527298048.
Definition PJ_RBR56 : Z := 9007199254740992000.

Definition PJ_HEAD : Z := 0x3dc08.
Definition PJ_KEY : Z := 0x3dcb8.
Definition PJ_DISP : Z := 0x3e2a0.
Definition PJ_NUMTAIL : Z := 0x3ec48.
Definition PJ_AV0 : Z := 0x3ed18.
Definition PJ_AV1 : Z := 0x3ed1c.

Record senv : Type := mkSE {
  e_LB0 : list block;  e_lo : Z;  e_B : Z;  e_q : Z;
  e_SB : Z;  e_DOC : Z;  e_TAPE : Z;  e_SBUF : Z;  e_len : Z;  e_tws : list Z;  e_sbs : list Z;
  e_j : Z;  e_c' : Z;
  e_ra : word;  e_gp : word;
  e_s0 : word;  e_s1 : word;  e_s2 : word;  e_s3 : word;  e_s4 : word;  e_s5 : word;
  e_s6 : word;  e_s7 : word;  e_s8 : word;  e_s9 : word;  e_s10 : word;  e_s11 : word;
  e_m0 : mem;  e_ps0 : PState }.

Notation e_T E := (Tf (e_tws E)).
Notation e_S E := (Tf (e_sbs E)).
Notation e_n E := (Z.of_nat (length (e_tws E))).
Notation e_sn E := (Z.of_nat (length (e_sbs E))).

Notation SST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (Z_to_bv 64 (e_q E + -256)) (e_gp E) (Z_to_bv 64 RATP) xt0 xt1 xt2 (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 (e_SB E))
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Notation LST E pc i dp xs3 xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m :=
  (SST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
       (Z_to_bv 64 i) xs3 (Z_to_bv 64 93) (Z_to_bv 64 dp) (Z_to_bv 64 PJ_RBK56) (Z_to_bv 64 (e_q E + -160)) xs8
       (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 107)
       xt3 xt4 xt5 xt6 F fc m).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition in_blocks (LB : list block) (A n : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b.

Record senv_ok (E : senv) : Prop := mkSEok {
  ok_wf : tape_wfS (e_T E) (e_S E) (e_sn E) ck_any (e_n E);
  ok_sbs : Forall (fun c => 0 <= c < 256) (e_sbs E);
  ok_tsz : 8 * e_n E <= SJ_TAPE (e_len E);
  ok_ssz : e_sn E <= SJ_SBUF (e_len E);
  ok_tape : in_blocks (e_LB0 E) (e_TAPE E) (8 * e_n E);
  ok_sbuf : in_blocks (e_LB0 E) (e_SBUF E) (e_sn E);
  ok_len : 0 <= e_len E <= SJ_PADMAX;
  ok_lo : alloc_ceiling <= e_lo E /\ GLOBALS_TOP <= e_lo E;
  ok_q : e_lo E + 256 + PJ_GROW_STACK <= e_q E /\ e_q E <= e_B E;
  ok_B : e_B E < 2^63;
  ok_sb : e_q E <= e_SB E /\ e_SB E + 88 <= e_B E;
  ok_doc : e_q E <= e_DOC E /\ e_DOC E + 16 <= e_B E;
  ok_sep : e_SB E + 88 <= e_DOC E \/ e_DOC E + 16 <= e_SB E;
  ok_j : 1 <= e_j E <= e_n E;
  ok_c : 0 <= e_c' E <= e_sn E;

  ok_al : e_DOC E mod 8 = 0 /\ e_TAPE E mod 8 = 0 }.

Lemma senv_out : forall E, senv_ok E -> 41 * (e_j E - 1) + 6 * e_c' E + 2 <= PJ_OUTMAX (e_len E).
Proof.
  intros E OK. destruct OK.
  eapply (pj_out_bound (e_len E) (e_n E) (e_sn E) (e_j E) (e_c' E)); try eassumption. lia.
Qed.

Definition sgoal (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (ch : @chst bptr) (s : PState)
    : machine_state -> Prop :=
  fun ms => implM usegs (pj_part raw_malloc raw_free ps_so set_so_ps (ch_fuel ch) (e_len E) (ch_cap ch) (ch_blk ch)) s Q ms.

Definition ser_saved (E : senv) : list cell :=
  [C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
   C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)].

Definition ser_consts (E : senv) (e64 e72 e80 : word) : list cell :=
  [C8 (Z_to_bv 64 (18446744073709551775 - e_q E));
   C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1);
   C8 (Z_to_bv 64 PJ_PMASK); C8 (Z_to_bv 64 PJ_TMASK);
   C8 (Z_to_bv 64 (18446744073709551758 - e_q E));
   C8 e64; C8 e72; C8 e80;
   C8 (Z_to_bv 64 PJ_RBK56)].

Definition serW (E : senv) (st : sbst) : list (Z * Z) :=
  [(e_q E - 256, e_q E); (sb_buf st, sb_buf st + sb_cap st); (e_SB E + 64, e_SB E + 88)].

Definition sb_pure (E : senv) (st : sbst) : Prop :=
  (sb_fuel st <= PJ_FUEL)%nat
  /\ 64 * 2 ^ (sb_k st) <= sb_cap st <= PJ_CAPMAX (e_len E)
  /\ match sb_blk st with
     | None => sb_buf st = e_SB E /\ sb_cap st = 64 /\ sb_fuel st = PJ_FUEL
     | Some _ => rblock_range (sb_buf st) (sb_cap st)
     end.

Definition SREF (E : senv) (st : sbst) (s : PState) (m : mem) : Prop :=
  RHEAP s (sbblocks st ++ e_LB0 E) m
  /\ rauxv_ok m (e_B E)
  /\ lx_pres (e_LB0 E) (e_q E) [(e_SB E, e_SB E + 88)] (e_m0 E) m
  /\ bytes_at usegs m (e_TAPE E) (u64s (map (Z_to_bv 64) (e_tws E)))
  /\ bytes_at usegs m (e_SBUF E) (map (Z_to_bv 8) (e_sbs E))
  /\ rw_cells usegs m (e_DOC E) [C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_SBUF E))]
  /\ (exists errv : word, rw_cells usegs m LX_ERRNO [C4 errv])
  /\ ps_fa s = ps_fa (e_ps0 E) /\ ps_so s = ps_so (e_ps0 E)
  /\ sb_pure E st.

Definition SCUR (E : senv) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (m : mem) : Prop :=
  (exists (j0 : list byte), rw_cells usegs m (e_q E + -256) (CB 8 j0 :: C8 spill :: ser_consts E e64 e72 e80))
  /\ u8arr usegs m (e_q E + -160) isobj /\ length isobj = 16%nat
  /\ stk usegs m (e_q E + -144) (e_q E + -104)
  /\ rw_cells usegs m (e_q E + -104) (ser_saved E)
  /\ rw_cells usegs m (e_SB E + 64) [C8 (Z_to_bv 64 (sb_buf st)); C8 (Z_to_bv 64 (sb_size st)); C8 (Z_to_bv 64 (sb_cap st))]
  /\ 0 <= sb_size st <= sb_cap st
  /\ stk usegs m (sb_buf st) (sb_buf st + sb_cap st)
  /\ stk usegs m (e_SB E) (e_SB E + 64)
  /\ mem_inv usegs m
  /\ stk usegs m (e_lo E) (e_q E + -256).

Definition SERM (E : senv) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem) : Prop :=
  SREF E st s m /\ SCUR E e64 e72 e80 spill isobj st m.

Notation SERMC E spill isobj st s m :=
  (SERM E (Z_to_bv 64 PJ_ESC_TAB) (Z_to_bv 64 PJ_LIT_BS) (Z_to_bv 64 PJ_LIT_QU) spill isobj st s m).

Definition sb_resize (st : sbst) (size : Z) : sbst := mkSb (sb_buf st) size (sb_cap st) (sb_blk st) (sb_fuel st).

Definition av_pc_ok (pc : Z) : Prop := pc = PJ_AV0 \/ pc = PJ_AV1.

Definition av_K (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 : word) (isobj : list byte)
    (pc il dp bound : Z) : Prop :=
  forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (spill' : word)
         (xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERM E e64 e72 e80 spill' isobj st' s' m' -> frm0 fc' -> sb_size st' <= bound ->
    (pc = PJ_AV0 \/ xs3 = Z_to_bv 64 PJ_TMASK) ->
    evt usegs (sgoal E Q (sb_ch st') s')
        (LST E pc il dp xs3 (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F' fc' m').

Definition str_stmt : Prop :=
  forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i c l dp A : Z)
         (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERMC E spill isobj st s m -> frm0 fc ->
    1 <= i < e_n E -> e_T E i = tword t_str c -> str_at (e_S E) (e_sn E) c l ->
    sb_size st <= A -> A + (2 + 6 * l) <= PJ_OUTMAX (e_len E) ->
    av_K E Q (Z_to_bv 64 PJ_ESC_TAB) (Z_to_bv 64 PJ_LIT_BS) (Z_to_bv 64 PJ_LIT_QU) isobj PJ_AV1 i dp (A + (2 + 6 * l)) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3e780 i dp (Z_to_bv 64 PJ_NE_TAB) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 (Z_to_bv 64 34) (Z_to_bv 64 34) xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition disp_K (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (isobj : list byte) (i dp bound : Z) : Prop :=
  forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (spill' : word)
         (xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERMC E spill' isobj st' s' m' -> frm0 fc' -> sb_size st' <= bound ->
    evt usegs (sgoal E Q (sb_ch st') s')
        (LST E PJ_DISP i dp (Z_to_bv 64 PJ_NE_TAB) xs8 xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F' fc' m').

Definition key_stmt : Prop :=
  forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i c l dp A : Z)
         (xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERMC E spill isobj st s m -> frm0 fc ->
    1 <= i < e_n E -> e_T E i = tword t_str c -> str_at (e_S E) (e_sn E) c l ->
    sb_size st <= A -> A + (3 + 6 * l) <= PJ_OUTMAX (e_len E) ->
    disp_K E Q isobj (i + 1) dp (A + (3 + 6 * l)) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E PJ_KEY i dp (Z_to_bv 64 PJ_NE_TAB) xs8 xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition i64_stmt : Prop :=
  forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A : Z)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
    1 <= i -> i + 1 < e_n E ->
    sb_size st <= A -> A + 20 <= PJ_OUTMAX (e_len E) ->
    av_K E Q e64 e72 e80 isobj PJ_AV0 (i + 1) dp (A + 20) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3e2f4 i dp (Z_to_bv 64 PJ_TMASK) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition u64_stmt : Prop :=
  forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A : Z)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
    1 <= i -> i + 1 < e_n E ->
    sb_size st <= A -> A + 20 <= PJ_OUTMAX (e_len E) ->
    av_K E Q e64 e72 e80 isobj PJ_AV0 (i + 1) dp (A + 20) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3e660 i dp (Z_to_bv 64 PJ_TMASK) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition dbl_stmt : Prop :=
  forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A : Z)
         (xs3 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
    1 <= i -> i + 1 < e_n E ->
    sb_size st <= A -> A + 27 <= PJ_OUTMAX (e_len E) ->
    av_K E Q e64 e72 e80 isobj PJ_AV0 (i + 1) dp (A + 27) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E 0x3ec28 i dp xs3 (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 (Z_to_bv 64 100) (Z_to_bv 64 100) xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).

Definition atom_stmt (pc xpc N : Z) : Prop :=
  forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A : Z)
         (xs3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
    sb_size st <= A -> A + N <= PJ_OUTMAX (e_len E) ->
    av_K E Q e64 e72 e80 isobj xpc i dp (A + N) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E pc i dp xs3 (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
Definition true_stmt : Prop := atom_stmt 0x3e564 PJ_AV0 4.
Definition false_stmt : Prop := atom_stmt 0x3e40c PJ_AV1 5.
Definition null_stmt : Prop := atom_stmt 0x3e5dc PJ_AV0 4.

End WithCeiling0.

Notation SERMC E spill isobj st s m :=
  (SERM E (Z_to_bv 64 PJ_ESC_TAB) (Z_to_bv 64 PJ_LIT_BS) (Z_to_bv 64 PJ_LIT_QU) spill isobj st s m).
