(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition ADS_CTOR   : Z := 0xf6d14.
Definition ADS_DTOR   : Z := 0xfc9b0.
Definition APDIAG     : Z := 0xeeb80.
Definition APDIAG_E   : Z := 0xeeb80.
Definition APUT_CSEQ  : Z := 0xf62a0.
Definition APUT_U16   : Z := 0x124e6c.
Definition APUT_U32   : Z := 0x12523c.
Definition APUT_U64   : Z := 0x12540c.
Definition APUT_INT   : Z := 0x12503c.
Definition AEXHAUSTED : Z := 0xf8bfc.

Definition DS_SIZE   : Z := 392.
Definition DS_ERR_OFF : Z := 360.
Definition DS_MAXBLK : Z := 2 ^ 28.
Definition DS_MAXLEN : Z := 2 ^ 24.
Definition DS_FL0    : Z := 4098.
Definition DS_FLHEX  : Z := 4104.
Definition DS_VBOFF  : Z := 112.

Definition ADS_STACK : Z := 16384.

Definition DS_FRAMES : nat := 6.

Definition ds_cost (len' : Z) : Z := 4 * (4 * len' + 96).

Definition DS_PF : list (Z * list Z) := [].

Definition DS_DTOR_PF : list (Z * list Z) := [(APC0_FREE, [0xfd148])].

Definition DS_EXH_PF : list (Z * list Z) := [(APC0_FREE, [0xfd148; 0xf8f14])].

Definition app_obj (O n : Z) : Prop := AIMG_TOP <= O /\ (O + n <= ALOWSH_LO \/ AHI_LO <= O) /\ O + n <= AAPP_HI.

Definition ds_xfer (LB B LB' B' : list block) : Prop :=
  exists LR, Permutation LB (B ++ LR) /\ Permutation LB' (B' ++ LR).

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Variable LINV : mem -> Prop.

  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.

  Definition ds_tr_ok : Prop := trace_ok (as_TR H) APC0_FREE [0x1200e8].

  Record ds_rep_lawsA : Prop := DS_REP_LAWS_A {
    dla_blocks : forall LB m ds err len B, ds_repA LB m ds err len B ->
        (length B <= 1)%nat /\ (forall b, In b B -> In b LB /\ 0 < blk_size b <= DS_MAXBLK);
    dla_err : forall LB m ds err len B, ds_repA LB m ds err len B ->
        rw_cells asegs m (ds + DS_ERR_OFF) [C4 (Z_to_bv 64 (err mod 2 ^ 32))];
    dla_def : forall LB m ds err len B, ds_repA LB m ds err len B ->
        addressable m ds DS_SIZE /\ 0 < ds /\ ds mod 8 = 0 /\ ds + DS_SIZE <= 2 ^ 47 /\ 0 <= len;
    dla_mono : forall LB m ds err len len' B, ds_repA LB m ds err len B -> len <= len' -> ds_repA LB m ds err len' B;

    dla_frame : forall LB LB' m m' ds err len B, ds_repA LB m ds err len B ->
        (forall a, 0 <= a < 2 ^ 64 ->
           (ds <= a < ds + DS_SIZE \/ in_block B a \/ in_block_sh B a \/ (sh ds <= a < sh ds + nsh DS_SIZE)) ->
           m' (wa a) = m (wa a)) ->
        (forall b, In b B -> In b LB') -> ds_repA LB' m' ds err len B;

    dla_hex : forall LB m ds err len B, LINV m -> ACONST m -> ds_repA LB m ds err len B ->
        exists vt fl, rw_cells asegs m ds [C8 (Z_to_bv 64 vt)] /\ ro_cells asegs m (vt - 24) [C8 (Z_to_bv 64 DS_VBOFF)]
                     /\ accessible m (vt - 24) 8
                     /\ (fl = DS_FL0 \/ fl = DS_FLHEX)
                     /\ rw_cells asegs m (ds + DS_VBOFF + 8) [C4 (Z_to_bv 64 fl)] /\
        forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (ds + DS_VBOFF + 8 <= a < ds + DS_VBOFF + 12) -> m' (wa a) = m (wa a)) ->
                   rw_cells asegs m' (ds + DS_VBOFF + 8) [C4 (Z_to_bv 64 DS_FLHEX)] ->
                   ds_repA LB m' ds err len B
  }.

  Definition ds_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB LBk : list block) (LF : list fframe) (X : list (Z * Z)) (cost lo B shi : Z) (m : mem) (mo : Model)
      (res : option Z) (Q : list block -> mem -> Prop) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                    (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ (forall d, res = Some d -> a0 = Z_to_bv 64 d)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Q LB' m'
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LBk (bv_unsigned sp) (X ++ XS) m m'

      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ LINV m'
      /\ as_AL H s' >= as_AL H s - cost.

  Definition ds_pre (entry : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
      (s : as_St H) (LB DB : list block) (LF : list fframe) (CH : list (Z * Z)) (cost lo B shi : Z) (errv : word) : Prop :=
       as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 entry) fc None m (seg_rom asegs)
    /\ frm_zero fc

    /\ as_RHEAP H s LB m /\ as_AKREL H s (mkCfg msF mo) /\ lb_own DB m
    /\ lb_small LB + 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 1 <= RT_LARGE_MAX
    /\ as_rauxv_ok H m B /\ bv_unsigned sp <= B /\ B < 2 ^ 64

    /\ bv_unsigned sp mod 16 = 0
    /\ stk asegs m lo (bv_unsigned sp) /\ aceil <= lo /\ lo <= bv_unsigned sp - ADS_STACK
    /\ rw_cells asegs m (errno_addr tp) [C4 errv] /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP
    /\ bv_unsigned ra mod 2 = 0
    /\ LINV m

    /\ ACONST m
    /\ as_RFS H LF m /\ (length LF + DS_FRAMES <= AFS_MAXLIVE_BP)%nat
    /\ stack0 m lo shi /\ bv_unsigned sp <= shi
    /\ as_chain H m (bv_unsigned s0) CH /\ pf_ok (as_TR H) DS_PF (bv_unsigned ra) CH
    /\ (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp')
    /\ ds_tr_ok
    /\ cost <= as_AL H s.

  Definition obj_inframe (LF : list fframe) (O n : Z) : Prop :=
    exists f, In f LF /\ ff_addr f <= O /\ O + n <= ff_addr f + fsz (ff_class f).

  Definition ds_obj (LF : list fframe) (m : mem) (sp O n : Z) : Prop :=
    addressable m O n /\ O mod 8 = 0 /\ fsobj H LF O n /\ 0 < O /\ O + n <= 2 ^ 47
    /\ (O + n <= sp - ADS_STACK \/ sp <= O) /\ app_obj O n.

  Definition ds_ctor_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (ds ppos pcons pstr pstr2 err : Z) (pos : list word) (j1 : list byte) (j2 : list byte),
      ds_pre ADS_CTOR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB [] LF CH 0 lo B shi errv ->
      a0 = Z_to_bv 64 ds -> a1 = Z_to_bv 64 ppos -> a2 = Z_to_bv 64 pcons -> a3 = Z_to_bv 64 pstr ->
      a4 = Z_to_bv 64 (err mod 2 ^ 64) -> a5 = Z_to_bv 64 pstr2 -> - 2 ^ 31 <= err < 0 ->
      ds_obj LF m (bv_unsigned sp) ds DS_SIZE -> wr_at asegs m ds DS_SIZE -> obj_inframe LF ds DS_SIZE ->
      ds_obj LF m (bv_unsigned sp) ppos 24 -> u64arr asegs m ppos pos -> length pos = 3%nat -> obj_inframe LF ppos 24 ->
      ds_obj LF m (bv_unsigned sp) pstr 24 -> rw_cells asegs m pstr [C2 (Z_to_bv 64 0); CB 22 j1] -> obj_inframe LF pstr 24 ->
      ds_obj LF m (bv_unsigned sp) pstr2 24 -> rw_cells asegs m pstr2 [C2 (Z_to_bv 64 0); CB 22 j2] -> obj_inframe LF pstr2 24 ->
      ds_obj LF m (bv_unsigned sp) pcons 48 -> rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)] ->
      (forall a, ds <= a < ds + DS_SIZE -> ~ (ppos <= a < ppos + 24) /\ ~ (pstr <= a < pstr + 24) /\ ~ (pstr2 <= a < pstr2 + 24)
                                        /\ ~ (pcons <= a < pcons + 48)) ->
      as_SR H (ds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB LF [(ds, ds + DS_SIZE)] 0 lo B shi m mo None
                       (fun LB' m' => Permutation LB' LB /\ ds_repA LB' m' ds err 0 [] /\ wr_at asegs m' ds DS_SIZE))
              (mkCfg msF mo).

  Definition pdiag_stmtA (entry : Z) (with_err : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (ds p pcons icount err : Z),
      ds_pre entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB [] LF CH 0 lo B shi errv ->
      a0 = Z_to_bv 64 ds -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 (err mod 2 ^ 64) ->
      (if with_err then - 2 ^ 31 <= err < 0 else err = - 4) ->
      ds_obj LF m (bv_unsigned sp) (p + 8) 8 -> ro_cells asegs m (p + 8) [C8 (Z_to_bv 64 pcons)] ->
      ds_obj LF m (bv_unsigned sp) (p + 80) 8 -> ro_cells asegs m (p + 80) [C8 (Z_to_bv 64 icount)] ->
      0 <= icount < 2 ^ 63 -> pcons mod 16 = 0 ->
      ds_obj LF m (bv_unsigned sp) ds DS_SIZE -> wr_at asegs m ds DS_SIZE -> obj_inframe LF ds DS_SIZE ->
      ds_obj LF m (bv_unsigned sp) pcons 48 -> rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)] ->
      (forall a, ds <= a < ds + DS_SIZE -> ~ (pcons <= a < pcons + 48)) ->
      as_SR H (ds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB LF [(ds, ds + DS_SIZE)] 0 lo B shi m mo None
                       (fun LB' m' => Permutation LB' LB /\ ds_repA LB' m' ds err 0 [] /\ wr_at asegs m' ds DS_SIZE))
              (mkCfg msF mo).
  Definition pdiag0_stmtA : Prop := pdiag_stmtA APDIAG false.
  Definition pdiagE_stmtA : Prop := pdiag_stmtA APDIAG_E true.

  Definition ds_op_Q (LB : list block) (B : list block) (ds err len' : Z) : list block -> mem -> Prop :=
    fun LB' m' => exists B', ds_xfer LB B LB' B' /\ ds_repA LB' m' ds err len' B' /\ lb_own B' m' /\ wr_at asegs m' ds DS_SIZE.

  Definition srcx_keep (LBk : list block) (LF : list fframe) (spz : Z) (X : list (Z * Z)) (m : mem) (p n : Z) : Prop :=
    exists bs, length bs = Z.to_nat n /\
      forall m' XS (s' : as_St H) (LB' : list block),
        ACONST m' -> mem_inv asegs m' -> Forall (fs_scratch H LF) XS -> xpres H LBk spz (X ++ XS) m m' ->
        as_RHEAP H s' LB' m' -> (forall b, In b LBk -> In b LB') ->
        bytes_at asegs m' p bs /\ accessible m' p n /\ shvis m' p (p + n).

  Definition put_cseq_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBk : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (ds err len p n : Z) (DB : list block),
      ds_pre APUT_CSEQ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB DB LF CH (ds_cost (len + n)) lo B shi errv ->
      a0 = Z_to_bv 64 ds -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 n ->
      ds_repA LB m ds err len DB -> Permutation LB (DB ++ LBk) ->
      ds_obj LF m (bv_unsigned sp) ds DS_SIZE -> obj_inframe LF ds DS_SIZE ->
      0 <= n -> (0 < p \/ n = 0) -> srcx_keep LBk LF (bv_unsigned sp) [(ds, ds + DS_SIZE)] m p n -> in_app_mem p (p + n) ->
      (p + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= p) ->
      (forall a, p <= a < p + n -> ~ (ds <= a < ds + DS_SIZE) /\ ~ in_block DB a) ->
      len + n <= DS_MAXLEN ->
      lb_small LB + 2 * 64512 <= RT_SMALL_MAX -> nlarge LB + 2 <= RT_LARGE_MAX ->
      as_SR H (ds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE)] (ds_cost (len + n))
                       lo B shi m mo (Some ds) (ds_op_Q LB DB ds err (len + n)))
              (mkCfg msF mo).

  Definition put_num_stmtA (entry lo_x hi_x : Z) (enc : Z -> Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBk : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (ds err len x : Z) (DB : list block),
      ds_pre entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB DB LF CH (ds_cost (len + 24)) lo B shi errv ->
      a0 = Z_to_bv 64 ds -> a1 = Z_to_bv 64 (enc x) -> lo_x <= x < hi_x ->
      ds_repA LB m ds err len DB -> Permutation LB (DB ++ LBk) ->
      ds_obj LF m (bv_unsigned sp) ds DS_SIZE -> obj_inframe LF ds DS_SIZE ->
      len + 24 <= DS_MAXLEN ->
      lb_small LB + 2 * 64512 <= RT_SMALL_MAX -> nlarge LB + 2 <= RT_LARGE_MAX ->

      as_SR H (ds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] (ds_cost (len + 24))
                       lo B shi m mo (Some ds) (ds_op_Q LB DB ds err (len + 24)))
              (mkCfg msF mo).
  Definition sx32 (x : Z) : Z := if x <? 2 ^ 31 then x else x + (2 ^ 64 - 2 ^ 32).
  Definition put_u16_stmtA : Prop := put_num_stmtA APUT_U16 0 (2 ^ 16) (fun x => x).
  Definition put_u32_stmtA : Prop := put_num_stmtA APUT_U32 0 (2 ^ 32) sx32.
  Definition put_u64_stmtA : Prop := put_num_stmtA APUT_U64 0 (2 ^ 64) (fun x => x).

  Definition put_int_stmtA : Prop := put_num_stmtA APUT_INT 0 (2 ^ 31) (fun x => x mod 2 ^ 64).

  Definition ds_dtor_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBk : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (ds err len : Z) (DB : list block),
      ds_pre ADS_DTOR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB DB LF CH 0 lo B shi errv ->
      pf_ok (as_TR H) DS_DTOR_PF (bv_unsigned ra) CH ->
      a0 = Z_to_bv 64 ds ->
      ds_repA LB m ds err len DB -> Permutation LB (DB ++ LBk) ->
      ds_obj LF m (bv_unsigned sp) ds DS_SIZE -> obj_inframe LF ds DS_SIZE ->
      as_SR H (ds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE)] 0 lo B shi m mo None
                       (fun LB' m' => Permutation LB' LBk /\ addressable m' ds DS_SIZE /\ wr_at asegs m' ds DS_SIZE))
              (mkCfg msF mo).

  Definition exhausted_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (this pcons nwords widx icount inst_offset opcode type : Z),
      ds_pre AEXHAUSTED ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB [] LF CH (2 ^ 20) lo B shi errv ->

      lo <= bv_unsigned sp - (ADS_STACK + 1024) -> (length LF + S DS_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      lb_small LB + 3 * 64512 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 3 <= RT_CNT_MAX -> nlarge LB + 3 <= RT_LARGE_MAX ->
      pf_ok (as_TR H) DS_EXH_PF (bv_unsigned ra) CH ->
      a0 = Z_to_bv 64 this -> a1 = Z_to_bv 64 inst_offset -> a2 = Z_to_bv 64 opcode -> a3 = Z_to_bv 64 type ->
      0 <= inst_offset < 2 ^ 63 -> 0 <= opcode < 2 ^ 16 -> 0 <= type < 2 ^ 32 ->
      ds_obj LF m (bv_unsigned sp) this 288 -> obj_inframe LF this 288 ->
      rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)] -> rw_cells asegs m (this + 56) [C8 (Z_to_bv 64 nwords)] ->
      rw_cells asegs m (this + 72) [C8 (Z_to_bv 64 widx)] -> rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 icount)] ->
      0 <= nwords < 2 ^ 63 -> 0 <= widx < 2 ^ 63 -> 0 <= icount < 2 ^ 63 ->
      ds_obj LF m (bv_unsigned sp) pcons 48 -> obj_inframe LF pcons 48 -> rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)] ->
      pcons mod 16 = 0 ->
      as_SR H (ds_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB LF
                       [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] (2 ^ 20) lo B shi m mo
                       (Some (2 ^ 64 - 4)) (fun LB' m' => Permutation LB' LB))
              (mkCfg msF mo).

  Record diag_pkgA : Prop := DIAG_PKG_A {
    dpa_laws : ds_rep_lawsA;
    dpa_ctor : ds_ctor_stmtA;
    dpa_pdiag0 : pdiag0_stmtA; dpa_pdiagE : pdiagE_stmtA;
    dpa_cseq : put_cseq_stmtA;
    dpa_u16 : put_u16_stmtA; dpa_u32 : put_u32_stmtA; dpa_u64 : put_u64_stmtA; dpa_int : put_int_stmtA;
    dpa_dtor : ds_dtor_stmtA;
    dpa_exhausted : exhausted_stmtA
  }.
End Stmts.
