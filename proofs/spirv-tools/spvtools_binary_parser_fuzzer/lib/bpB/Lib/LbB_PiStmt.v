From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition pi_nodes (c : pmc) : Z := Zlen (t3c (c_m1 c)) + Zlen (t3c (c_m2 c)) + Zlen (t3c (c_m3 c)).
Definition pi_m3ok (ents : list (Z * (Z * Z))) : Prop := Forall (fun e => 0 <= snd (snd e) < 2 ^ 31) ents.
Definition pi_m2ok (ents : list (Z * (Z * (Z * Z * Z)))) : Prop :=
  Forall (fun e => 0 <= t3a (snd (snd e)) < 4 /\ 0 <= t3c (snd (snd e)) < 16) ents.
Definition pi_macct (c : pmc) : Prop :=
  8 * t3b (c_m1 c) <= 16 * Zlen (t3c (c_m1 c)) + 504 /\ 8 * t3b (c_m2 c) <= 16 * Zlen (t3c (c_m2 c)) + 504 /\
  8 * t3b (c_m3 c) <= 16 * Zlen (t3c (c_m3 c)) + 504 /\ pi_m3ok (t3c (c_m3 c)) /\ pi_m2ok (t3c (c_m2 c)).
Definition pi_lacc (c : pmc) : Prop :=
  2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c.

Definition pi_stc (words n diag : Z) (c : pmc) : stateC :=
  {| st_words := words; st_nwords := n; st_diag := diag;
     st_widx := c_widx c; st_icount := c_icount c; st_endian := c_endian c; st_flags := c_reqconv c;
     st_m1 := c_m1 c; st_m2 := c_m2 c; st_m3 := c_m3 c;
     st_v1 := (t3a (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c));
     st_v2 := (t3a (c_v2 c), t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)), t3a (c_v2 c) + 4 * t3c (c_v2 c));
     st_v3 := (t3a (c_v3 c), t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)), t3a (c_v3 c) + 4 * t3c (c_v3 c)) |}.
Definition pi_prc (cons user words n diag : Z) (c : pmc) : parserC :=
  {| pc_cons := cons; pc_user := user; pc_state := pi_stc words n diag c |}.

Section PiStmt.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Record piw : Type := PIW {
    pw_p : Z; pw_cons : Z; pw_user : Z; pw_diag : Z; pw_words : Z; pw_n : Z;
    pw_LB0 : list block;
    pw_s0 : as_St H;
    pw_lo : Z; pw_B : Z; pw_shi : Z
  }.

  Record piw_ok (w : piw) (LF : list fframe) (m : mem) : Prop := PIW_OK {
    pk_pobj  : fsobj H LF (pw_p w) PARSER_SIZE;
    pk_pin   : exists f, In f LF /\ ff_addr f <= pw_p w /\ pw_p w + PARSER_SIZE <= ff_addr f + fsz (ff_class f);
    pk_papp  : aapp (pw_p w) PARSER_SIZE /\ 0 < pw_p w /\ pw_p w mod 16 = 0;
    pk_cobj  : fsobj H LF (pw_cons w) 48;
    pk_capp  : aapp (pw_cons w) 48 /\ 0 < pw_cons w /\ pw_cons w mod 16 = 0;
    pk_pcons : pw_p w + PARSER_SIZE <= pw_cons w \/ pw_cons w + 48 <= pw_p w;
    pk_cin   : exists f, In f LF /\ ff_addr f <= pw_cons w /\ pw_cons w + 48 <= ff_addr f + fsz (ff_class f);
    pk_meas0 : lb_small (pw_LB0 w) + po_small (pw_n w) <= RT_SMALL_MAX
               /\ Z.of_nat (length (pw_LB0 w)) + po_cnt (pw_n w) <= RT_CNT_MAX
               /\ nlarge (pw_LB0 w) + po_large (pw_n w) <= RT_LARGE_MAX;
    pk_words : words_okA (pw_LB0 w) m (pw_words w) (pw_n w);
    pk_n     : 0 <= pw_n w < 2 ^ 24;
    pk_B64   : pw_B w < 2 ^ 64;
    pk_diag  : 0 <= pw_diag w < 2 ^ 64
  }.

  Record PIX (w : piw) (s : as_St H) (LB LBs : list block) (m : mem) (c : pmc) : Prop := MKPIX {
    px_rheap  : as_RHEAP H s LB m;
    px_lbown  : lb_own LBs m;
    px_own    : Permutation LB (pw_LB0 w ++ LBs) /\ Permutation (lbl LBs) (c_blocks c);
    px_meas   : pm_meas_ok (pw_n w) LBs;
    px_meminv : mem_inv asegs m;
    px_errno  : exists errv : word, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv];
    px_rauxv  : as_rauxv_ok H m (pw_B w);
    px_aconst : ACONST m;
    px_stack0 : stack0 m (pw_lo w) (pw_shi w);
    px_linv   : LINV m;
    px_al     : as_AL H s >= as_AL H (pw_s0 w) - pm_phi c /\ pm_cap c + PM_RESERVE <= po_cost (pw_n w)
                /\ po_cost (pw_n w) <= as_AL H (pw_s0 w);

    px_pdef   : mdef m (pw_p w) PARSER_SIZE;
    px_cons   : fld ASEGS m (pw_p w + 8) 8 (pw_cons w);
    px_user   : fld ASEGS m (pw_p w + 16) 8 (pw_user w);
    px_hdrfn  : fld ASEGS m (pw_p w + 24) 8 0;
    px_insfn  : fld ASEGS m (pw_p w + 32) 8 0;
    px_hunk   : fld ASEGS m (pw_p w + 40) 1 0;
    px_words  : fld ASEGS m (pw_p w + O_WORDS) 8 (pw_words w);
    px_n      : fld ASEGS m (pw_p w + O_N) 8 (pw_n w);
    px_diag   : fld ASEGS m (pw_p w + O_DIAG) 8 (pw_diag w);
    px_widx   : fld ASEGS m (pw_p w + O_WIDX) 8 (c_widx c);
    px_icount : fld ASEGS m (pw_p w + O_ICOUNT) 8 (c_icount c);
    px_endian : fld ASEGS m (pw_p w + O_ENDIAN) 4 (c_endian c);
    px_flags  : fld ASEGS m (pw_p w + O_FLAGS) 1 (c_reqconv c);
    px_retry  : fld ASEGS m (pw_p w + O_FLAGS + 1) 1 0;
    px_scal   : 0 <= c_widx c <= pw_n w /\ 0 <= c_icount c <= c_widx c /\ 0 <= c_endian c < 2 ^ 32
                /\ (c_reqconv c = 0 \/ c_reqconv c = 1);
    px_consf  : fld ASEGS m (pw_cons w + 32) 8 0;
    px_consd  : mdef m (pw_cons w + 32) 8;
    px_consw  : wr_at asegs m (pw_cons w) 48;
    px_wbuf   : pw_words w <> 0 -> mdef m (pw_words w) (4 * pw_n w);

    px_m1 : @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (pw_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c));
    px_m2 : @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m (pw_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c));
    px_m3 : @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (pw_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c));
    px_v1 : @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m (pw_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c));
    px_v2 : @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (pw_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c));
    px_v3 : @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (pw_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c));
    px_sh : pmc_sh m c /\ addressable m (pw_p w) PARSER_SIZE /\ addressable m (pw_cons w) 48;

    px_tr   : c_tr c = [];
    px_bsz  : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    px_ic   : c_icount c + 5 <= c_widx c;
    px_end  : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    px_w    : pw_words w <> 0 /\ 5 <= pw_n w;
    px_bud  : pm_bud (pw_n w) c;
    px_acc  : pi_nodes c + 1 <= c_widx c + 3 /\ pi_macct c /\ pi_lacc c
  }.

  Definition pi_err (w : piw) (s : as_St H) (LB LBs : list block) (m : mem) (c : parserC) : Prop :=
    as_RHEAP H s LB m /\ state_own LB (pw_LB0 w) LBs (pc_state c) /\ lb_own LBs m
    /\ parser_repA LB m (pw_p w) c /\ parser_sh m (pw_p w) c
    /\ pc_cons c = pw_cons w /\ pc_user c = pw_user w
    /\ st_words (pc_state c) = pw_words w /\ st_nwords (pc_state c) = pw_n w
    /\ lb_small LBs + 2 ^ 12 <= po_small (pw_n w)
    /\ Z.of_nat (length LBs) + 8 <= po_cnt (pw_n w)
    /\ nlarge LBs + 3 <= po_large (pw_n w)
    /\ st_vsteps (pc_state c)
    /\ (forall q k, In (q, k) (state_blocks (pc_state c)) -> k <= 2 ^ 40)
    /\ mem_inv asegs m /\ (exists errv : word, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ as_rauxv_ok H m (pw_B w) /\ ACONST m /\ stack0 m (pw_lo w) (pw_shi w) /\ LINV m
    /\ as_AL H s >= as_AL H (pw_s0 w) - po_cost (pw_n w)
    /\ mdef m (pw_p w) PARSER_SIZE.

  Definition pi_post (w : piw) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (c : pmc) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 (r : Z) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' LBs' : list block)
                     (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc' /\ - 2 ^ 31 <= r < 2 ^ 31
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ stk asegs m' (pw_lo w) (bv_unsigned sp) /\ as_RFS H LF m' /\ piw_ok w LF m'
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H (pw_LB0 w) (bv_unsigned sp) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (pw_p w, pw_p w + PARSER_SIZE) :: XS) m m'
      /\ ((r = 0 /\ exists c' : pmc, PIX w s' LB' LBs' m' c' /\ c_widx c < c_widx c')
          \/ (r <> 0 /\ exists c' : parserC, pi_err w s' LB' LBs' m' c')).

  Definition parse_inst_stmtB : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (w : piw) (s : as_St H) (LB LBs : list block) (LF : list fframe) (CH : list (Z * Z)) (c : pmc),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 APM_ENTRY) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 (pw_p w) -> tp = Z_to_bv 64 ATP ->
      piw_ok w LF m -> PIX w s LB LBs m c -> c_widx c < pw_n w ->
      as_AKREL H s (mkCfg msF mo) ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= pw_B w -> bv_unsigned sp <= pw_shi w ->
      stk asegs m (pw_lo w) (bv_unsigned sp) -> aceil <= pw_lo w -> pw_lo w <= bv_unsigned sp - APM_STACK ->
      bv_unsigned ra mod 2 = 0 ->
      as_RFS H LF m -> (length LF + PM_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) PM_PF (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pm_tr_ok H ->
      as_SR H (pi_post w ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF c m mo) (mkCfg msF mo).
End PiStmt.
