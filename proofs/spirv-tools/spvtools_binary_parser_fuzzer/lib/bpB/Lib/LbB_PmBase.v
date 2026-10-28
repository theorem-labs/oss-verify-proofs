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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition APM_FRAME : Z := 832.
Definition PM_NSH : Z := 1448.
Definition PM_MAGIC : Z := 0x41b58ab3.
Definition PM_RETIRED : Z := 0x45e0360e.
Definition PM_DESC : Z := 0x1728f.

Definition PM_OBJS : list (Z * Z) :=
  [(32, 8); (64, 8); (96, 4); (112, 20); (176, 4); (192, 400); (656, 400); (1120, 400); (1584, 400); (2048, 400);
   (2512, 400); (2976, 8); (3008, 4); (3024, 16); (3056, 400); (3520, 4); (3536, 400); (4000, 8); (4032, 400);
   (4496, 16); (4528, 4); (4544, 400); (5008, 400); (5472, 400); (5936, 24); (6000, 400); (6464, 400); (6928, 8);
   (6960, 400); (7424, 16); (7456, 8); (7488, 400); (7952, 16); (7984, 8); (8016, 400); (8480, 16); (8512, 8);
   (8544, 16); (8576, 400); (9040, 40); (9120, 4); (9136, 2); (9152, 400); (9616, 8); (9648, 400); (10112, 8);
   (10144, 16); (10176, 400); (10640, 400); (11104, 400)].

Definition OB_PARSED_OPERAND : nat := 3.
Definition OB_INST : nat := 39.
Definition OB_FIRST_WORD : nat := 40.
Definition OB_INST_WC : nat := 41.
Definition OB_OPCODE_DESC : nat := 43.
Definition OB_INST_OFFSET : nat := 45.
Definition OB_WORD : nat := 4.

Definition S_MODULE : list nat := [].
Definition S_INSTR : list nat := [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC; OB_INST_OFFSET].
Definition S_OPER : list nat := OB_PARSED_OPERAND :: OB_WORD :: S_INSTR.

Definition pm_fsh (ins : list nat) : list byte := map (Z_to_bv 8) (fsh_pat PM_OBJS PM_NSH ins).

Definition ICM_LARGE : Z := 64512.
Definition pm_phi_blocks (bs : list (Z * Z)) : Z :=
  8 * fold_right (fun b acc => (if ICM_LARGE <? snd b then snd b else 0) + acc) 0 bs.

Definition PM_RESERVE : Z := 2 ^ 31.

Definition pm_meas_ok (n : Z) (LBs : list block) : Prop :=
  lb_small LBs + 2 ^ 18 <= po_small n /\ Z.of_nat (length LBs) + 8 <= po_cnt n /\ nlarge LBs + 3 <= po_large n.

Definition PM_STRK : Z := 64.
Definition pm_progz (widx : Z) : Z := PM_STRK * Z.min (Z.max 0 widx) (2 ^ 24).
Definition pm_prog (c : pmc) : Z := pm_progz (c_widx c).
Definition pm_phi (c : pmc) : Z := pm_phi_blocks (c_blocks c) + pm_prog c.

Definition pm_cap (c : pmc) : Z := pm_phi_blocks (c_blocks c) + 2 ^ 30.

Lemma pm_progz_bounds : forall i, 0 <= pm_progz i <= 2 ^ 30.
Proof. intros i. unfold pm_progz, PM_STRK. change (2 ^ 30) with (64 * 2 ^ 24). lia. Qed.
Lemma pm_prog_bounds : forall c, 0 <= pm_prog c <= 2 ^ 30.
Proof. intros c. apply pm_progz_bounds. Qed.
Lemma pm_progz_mono : forall i j, i <= j -> pm_progz i <= pm_progz j.
Proof. intros i j Hij. unfold pm_progz, PM_STRK. lia. Qed.
Lemma pm_progz_step : forall i k, 0 <= i -> 0 <= k -> i + k <= 2 ^ 24 -> pm_progz (i + k) = pm_progz i + PM_STRK * k.
Proof. intros i k Hi Hk Hik. unfold pm_progz, PM_STRK. lia. Qed.

Lemma pm_phi_eq : forall c, pm_phi c = pm_phi_blocks (c_blocks c) + pm_prog c.
Proof. reflexivity. Qed.

Lemma pm_phi_same_widx : forall c c', c_widx c' = c_widx c ->
  pm_phi c' - pm_phi c = pm_phi_blocks (c_blocks c') - pm_phi_blocks (c_blocks c).
Proof. intros c c' E. unfold pm_phi, pm_prog. rewrite E. lia. Qed.

Lemma pm_phi_ge_blocks : forall c c' K, c_widx c' = c_widx c ->
  pm_phi_blocks (c_blocks c') >= pm_phi_blocks (c_blocks c) + K -> pm_phi c' >= pm_phi c + K.
Proof. intros c c' K E G. pose proof (pm_phi_same_widx c c' E). lia. Qed.
Lemma pm_phi_eq_blocks : forall c c' K, c_widx c' = c_widx c ->
  pm_phi_blocks (c_blocks c') = pm_phi_blocks (c_blocks c) + K -> pm_phi c' = pm_phi c + K.
Proof. intros c c' K E G. pose proof (pm_phi_same_widx c c' E). lia. Qed.
Lemma pm_phi_le_cap : forall c, pm_phi c <= pm_cap c.
Proof. intros c. unfold pm_phi, pm_cap. pose proof (pm_prog_bounds c). lia. Qed.
Lemma pm_cap_eq : forall c, pm_cap c = pm_phi_blocks (c_blocks c) + 2 ^ 30.
Proof. reflexivity. Qed.

Definition set_scalA (c : pmc) (widx icount endian reqconv : Z) : pmc :=
  {| c_widx := widx; c_icount := icount; c_endian := endian; c_reqconv := reqconv;
     c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.
Lemma set_scalA_id : forall c, set_scalA c (c_widx c) (c_icount c) (c_endian c) (c_reqconv c) = c.
Proof. intros []; reflexivity. Qed.

Definition WV_P : N := 32.  Definition WV_FF : N := 33.  Definition WV_SP0 : N := 34.  Definition WV_S1 : N := 35.
Definition WV_WORDS : N := 36.  Definition WV_N : N := 37.  Definition WV_CONS : N := 38.  Definition WV_USER : N := 39.
Definition WV_DIAG : N := 40.
Definition WV_LAST : N := 40.
Definition wvals (p ff sp0 s1 words n cons user diag : Z) : list word :=
  [Z_to_bv 64 p; Z_to_bv 64 ff; Z_to_bv 64 sp0; Z_to_bv 64 s1; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 cons;
   Z_to_bv 64 user; Z_to_bv 64 diag].

Fixpoint wclosed (e : SX2.expr) : bool :=
  match e with
  | SX2.ELit _ => true
  | SX2.EVar n => (32 <=? n)%N && (n <=? 40)%N
  | SX2.EAlu _ a b | SX2.EAluw _ a b | SX2.EMd _ a b | SX2.EMdw _ a b => wclosed a && wclosed b
  | SX2.EExt _ _ _ a => wclosed a
  | SX2.EBlob _ _ _ _ => false
  end.

Section Ctx.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Record pmwA : Type := PMWA {
    wa_p : Z; wa_cons : Z; wa_user : Z; wa_diag : Z; wa_words : Z; wa_n : Z;
    wa_sp0 : Z;
    wa_s1 : Z;
    wa_ff : Z; wa_fp : Z;
    wa_ra : Z;
    wa_saved : list word;
    wa_gp : word; wa_tp : word;
    wa_LB0 : list block;
    wa_LF0 : list fframe;
    wa_CH : list (Z * Z);
    wa_m0 : mem; wa_mo0 : Model; wa_s0 : as_St H;
    wa_lo : Z; wa_B : Z; wa_shi : Z
  }.

  Definition wenv_vals (w : pmwA) : list word :=
    wvals (wa_p w) (wa_ff w) (wa_sp0 w) (wa_s1 w) (wa_words w) (wa_n w) (wa_cons w) (wa_user w) (wa_diag w).

  Definition slots_ok (w : pmwA) (m : mem) (R0 : bvmap 5 word) (tbl : list (Z * SX2.expr)) : Prop :=
    Forall (fun ke => rw_cells asegs m (wa_s1 w + fst ke) [C8 (SX2.edenot (HLib.Eseed R0 (wenv_vals w)) (snd ke))]) tbl.

  Definition fslots_ok (w : pmwA) (m : mem) (tbl : list (Z * SX2.expr)) : Prop :=
    Forall (fun ke => rw_cells asegs m (wa_ff w + fst ke) [C8 (SX2.edenot (HLib.Eseed bvmap_empty (wenv_vals w)) (snd ke))]) tbl.

  Definition vsh_opnd (m : mem) (v : Z * Z * Z) : Prop :=
    t3a v <> 0 -> SHAD m (t3a v) (cc_gen (OPND_SZ * t3c v) (OPND_SZ * t3b v)).
  Definition vsh32 (m : mem) (v : Z * list Z * Z) : Prop :=
    t3a v <> 0 -> SHAD m (t3a v) (cc_gen (4 * t3c v) (4 * Zlen (t3b v))).
  Definition pmc_sh (m : mem) (c : pmc) : Prop :=
    umap_sh m 24 (c_m1 c) /\ umap_sh m 32 (c_m2 c) /\ umap_sh m 24 (c_m3 c)
    /\ vsh_opnd m (c_v1 c) /\ vsh32 m (c_v2 c) /\ vsh32 m (c_v3 c).

  Record PMXAT (w : pmwA) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc) (ins : list nat)
              (tbl ftbl : list (Z * SX2.expr)) (TB : list block) (spal : Z) : Prop := MKPMXA {

    xa_rheap  : as_RHEAP H s LB m;
    xa_lbown  : lb_own LBs m;
    xa_tb     : lb_own TB m /\ (length TB <= 1)%nat;
    xa_own    : Permutation LB (wa_LB0 w ++ LBs ++ TB) /\ Permutation (lbl LBs) (c_blocks c);
    xa_meas   : pm_meas_ok (wa_n w) LBs;
    xa_mpres  : as_MPRES H (wa_mo0 w) mo;
    xa_meminv : mem_inv asegs m;
    xa_stk    : stk asegs m (wa_lo w) (wa_sp0 w);
    xa_errno  : exists errv : word, rw_cells asegs m (errno_addr (wa_tp w)) [C4 errv];
    xa_rauxv  : as_rauxv_ok H m (wa_B w);
    xa_aconst : ACONST m;
    xa_stack0 : stack0 m (wa_lo w) (wa_shi w);
    xa_linv   : LINV m;
    xa_rfs    : as_RFS H ((PM_FCLASS, wa_ff w, wa_fp w) :: wa_LF0 w) m;
    xa_xpres  : exists XS, Forall (fs_scratch H (wa_LF0 w)) XS
                           /\ xpres H (wa_LB0 w) (wa_sp0 w)
                                ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (wa_p w, wa_p w + PARSER_SIZE) :: (wa_ff w, wa_ff w + fsz PM_FCLASS)
                                 :: (sh (wa_ff w), sh (wa_ff w) + fshn PM_FCLASS) :: XS) (wa_m0 w) m;
    xa_al     : as_AL H s >= as_AL H (wa_s0 w) - pm_phi c - spal /\ pm_cap c + PM_RESERVE <= po_cost (wa_n w)
                /\ po_cost (wa_n w) <= as_AL H (wa_s0 w) /\ 0 <= spal <= PM_RESERVE;

    xa_saved  : rw_cells asegs m (wa_sp0 w - 104) (map C8 (wa_saved w));
    xa_fhdr   : rw_cells asegs m (wa_ff w) [C8 (Z_to_bv 64 PM_MAGIC); C8 (Z_to_bv 64 PM_DESC); C8 (Z_to_bv 64 APM_ENTRY)];
    xa_fflag  : rw_cells asegs m (wa_ff w + fsz PM_FCLASS - 8) [C8 (Z_to_bv 64 (wa_fp w))];
    xa_fwr    : wr_at asegs m (wa_ff w) (fsz PM_FCLASS);
    xa_chain  : as_chain H m (wa_sp0 w) ((wa_sp0 w, wa_ra w) :: wa_CH w);
    xa_fsh    : SHAD m (wa_ff w) (pm_fsh ins);
    xa_slots  : slots_ok w m (bvmap_empty) tbl;
    xa_fslots : fslots_ok w m ftbl;

    xa_pdef   : mdef m (wa_p w) PARSER_SIZE;
    xa_cons   : fld ASEGS m (wa_p w + 8) 8 (wa_cons w);
    xa_user   : fld ASEGS m (wa_p w + 16) 8 (wa_user w);
    xa_hdrfn  : fld ASEGS m (wa_p w + 24) 8 0;
    xa_insfn  : fld ASEGS m (wa_p w + 32) 8 0;
    xa_hunk   : fld ASEGS m (wa_p w + 40) 1 0;
    xa_words  : fld ASEGS m (wa_p w + O_WORDS) 8 (wa_words w);
    xa_n      : fld ASEGS m (wa_p w + O_N) 8 (wa_n w);
    xa_diag   : fld ASEGS m (wa_p w + O_DIAG) 8 (wa_diag w);
    xa_widx   : fld ASEGS m (wa_p w + O_WIDX) 8 (c_widx c);
    xa_icount : fld ASEGS m (wa_p w + O_ICOUNT) 8 (c_icount c);
    xa_endian : fld ASEGS m (wa_p w + O_ENDIAN) 4 (c_endian c);
    xa_flags  : fld ASEGS m (wa_p w + O_FLAGS) 1 (c_reqconv c);
    xa_retry  : fld ASEGS m (wa_p w + O_FLAGS + 1) 1 0;
    xa_scal   : 0 <= c_widx c <= wa_n w /\ 0 <= c_icount c <= c_widx c /\ 0 <= c_endian c < 2 ^ 32
                /\ (c_reqconv c = 0 \/ c_reqconv c = 1);
    xa_consf  : fld ASEGS m (wa_cons w + 32) 8 0;
    xa_consd  : mdef m (wa_cons w + 32) 8;
    xa_consw  : wr_at asegs m (wa_cons w) 48;
    xa_wbuf   : wa_words w <> 0 -> mdef m (wa_words w) (4 * wa_n w);

    xa_m1 : @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (wa_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c));
    xa_m2 : @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m (wa_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c));
    xa_m3 : @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (wa_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c));
    xa_v1 : @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c));
    xa_v2 : @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c));
    xa_v3 : @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c));
    xa_sh : pmc_sh m c /\ addressable m (wa_p w) PARSER_SIZE /\ addressable m (wa_cons w) 48
  }.
End Ctx.

Arguments wa_p {H} _.
Arguments wa_cons {H} _.
Arguments wa_user {H} _.
Arguments wa_diag {H} _.
Arguments wa_words {H} _.
Arguments wa_n {H} _.
Arguments wa_sp0 {H} _.
Arguments wa_s1 {H} _.
Arguments wa_ff {H} _.
Arguments wa_fp {H} _.
Arguments wa_ra {H} _.
Arguments wa_saved {H} _.
Arguments wa_gp {H} _.
Arguments wa_tp {H} _.
Arguments wa_LB0 {H} _.
Arguments wa_LF0 {H} _.
Arguments wa_CH {H} _.
Arguments wa_m0 {H} _.
Arguments wa_mo0 {H} _.
Arguments wa_s0 {H} _.
Arguments wa_lo {H} _.
Arguments wa_B {H} _.
Arguments wa_shi {H} _.
Arguments wenv_vals {H} _.
Arguments slots_ok {H} _ _ _ _.
Arguments fslots_ok {H} _ _ _.
Arguments PMXAT {HCEIL} H LINV w s LB LBs m mo c ins tbl ftbl TB spal.

Notation PMXA H LINV w s LB LBs m mo c ins tbl ftbl := (PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] 0).
Arguments MKPMXA {HCEIL H LINV w s LB LBs m mo c ins tbl ftbl TB spal}.
