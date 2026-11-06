(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module WdLibc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_WdLibc () := "C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module WDL.

(* [comment removed for export] *)
Definition SNP_BUF : Z := 100.          (* [comment removed for export] *)
Definition SNP_MAX : Z := 26.           (* [comment removed for export] *)
Definition SNP_SCR : Z := 8192.         (* [comment removed for export] *)
Definition STRTOD_SCR : Z := 10240.     (* [comment removed for export] *)
Definition FMT_G_PLAIN : Z := 0x12c0b.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dbl_nz (d : Z) : Prop := 0 <= d < 2 ^ 64 /\ d mod 2 ^ 63 <> 0.

(* [comment removed for export] *)
Definition isdig (c : Z) : bool := (48 <=? c) && (c <=? 57).
Fixpoint skip_digits (bs : list Z) : list Z :=
  match bs with c :: r => if isdig c then skip_digits r else bs | [] => [] end.
Definition ndig (bs : list Z) : nat := (length bs - length (skip_digits bs))%nat.
Definition gnum_exp (bs : list Z) : bool :=          (* [comment removed for export] *)
  match bs with
  | c :: r => ((c =? 43) || (c =? 45)) && (2 <=? ndig r)%nat && (length (skip_digits r) =? 0)%nat
  | [] => false
  end.
Definition gnum_tail (bs : list Z) : bool :=         (* [comment removed for export] *)
  match bs with [] => true | c :: r => (c =? 101) && gnum_exp r end.
Definition gnum_frac (bs : list Z) : bool :=         (* [comment removed for export] *)
  match bs with
  | c :: r => if c =? 46 then (1 <=? ndig r)%nat && gnum_tail (skip_digits r) else gnum_tail bs
  | [] => true
  end.
Definition gnum (bs : list Z) : bool :=
  let bs1 := match bs with c :: r => if c =? 45 then r else bs | [] => bs end in
  (1 <=? ndig bs1)%nat && gnum_frac (skip_digits bs1).

(* [comment removed for export] *)
Definition gspecial (bs : list Z) : Prop :=
  bs = [105; 110; 102] \/ bs = [45; 105; 110; 102] \/ bs = [110; 97; 110] \/ bs = [45; 110; 97; 110].

Example gnum_ex1 : gnum [49; 46; 53; 101; 45; 48; 55] = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdLibc ()) [] "p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8g000mj20Tg001Gg001g'0o"). Qed.
Example gnum_ex2 : gnum [45; 48; 46; 48; 48; 48; 49; 50; 51] = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdLibc ()) [] "p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8g000mj20Tg001Gg001g'0o"). Qed.
Example gnum_ex3 : gnum [49; 50; 51; 52; 53; 54] = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdLibc ()) [] "p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8g000mj20Tg001Gg001g'0o"). Qed.
Example gnum_ex4 : gnum [49; 101; 43; 50; 49] = true.
Proof.
ltac2:(KReplay.run1 (kr_t_WdLibc ()) [] "p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8g000mj20Tg001Gg001g'0o"). Qed.

Section Libc.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

(* [comment removed for export] *)
Definition entry_scr (R : bvmap 5 word) (M : word -> option byte) (sp r scr : Z) : Prop :=
  getr R 1%bv = Z_to_bv 64 r /\ L5.ra_ok r /\ getr R 2%bv = Z_to_bv 64 sp /\ getr R 3%bv = Z_to_bv 64 (pa_gp A)
  /\ getr R 4%bv = Z_to_bv 64 (pa_tp A) /\ L5C.stk (hl_sptop L) M sp scr.

(* [comment removed for export] *)
Definition fregs_preserved (fx fx' : FPState) : Prop :=
  (forall r : bv 5, In (bv_unsigned r) [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (@fp_regs fx') r = getr (@fp_regs fx) r)
  /\ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7.

(* [comment removed for export] *)
Definition mframe (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - scr <= a < sp) -> L5.outside W a -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a : word, M a <> None -> M' a <> None)
  /\ L5.defined M' (sp - scr) scr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition snprintf_spec (pc fmt : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (buf prec d sp r : Z),
    PMSP.model_ok model -> K [] ->
    entry_scr R M sp r SNP_SCR ->
    getr R 10%bv = Z_to_bv 64 buf -> getr R 11%bv = Z_to_bv 64 SNP_BUF -> getr R 12%bv = Z_to_bv 64 fmt ->
    getr R 13%bv = Z_to_bv 64 prec -> getr R 14%bv = Z_to_bv 64 d ->
    (prec = 15 \/ prec = 17) -> dbl_nz d ->
    sp <= buf -> buf + SNP_BUF <= hl_sptop L -> L5.defined M buf SNP_BUF ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n : Z) (bs : list Z),
        regs_preserved R R' -> fregs_preserved fx fx' -> getr R' 10%bv = Z_to_bv 64 n ->
        1 <= n <= SNP_MAX -> Z.of_nat (length bs) = n -> (gnum bs = true \/ gspecial bs) -> Forall (fun c => 0 <= c < 256) bs ->
        L5.bytes_at segs M' buf (bs ++ [0]) ->
        mframe sp SNP_SCR [(buf, SNP_BUF)] M M' -> PMST.base_ok segs A M' ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strtod_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (s endp n sp r : Z) (bs : list Z),
    PMSP.model_ok model -> K [] ->
    entry_scr R M sp r STRTOD_SCR ->
    getr R 10%bv = Z_to_bv 64 s -> getr R 11%bv = Z_to_bv 64 endp ->
    Z.of_nat (length bs) = n -> 1 <= n <= SNP_MAX -> (gnum bs = true \/ gspecial bs) -> L5.bytes_at segs M s (bs ++ [0]) ->
    Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->     (* [comment removed for export] *)
    sp <= s -> s + n + 1 <= hl_sptop L ->
    sp <= endp -> endp + 8 <= hl_sptop L -> L5.defined M endp 8 -> (endp + 8 <= s \/ s + n + 1 <= endp) ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> fregs_preserved fx fx' ->
        L5.u64_at segs M' endp (s + n) -> L5.bytes_at segs M' s (bs ++ [0]) ->
        mframe sp STRTOD_SCR [(endp, 8)] M M' -> PMST.base_ok segs A M' ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

End Libc.
End WDL.

End WdLibc.
Module FrmGuard.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.WdLibc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMG.
Section G.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.

Lemma cps_of_msteps_fz (fx fx' : FPState) R pc M R' pc' M' model K :
  m_halted model = None -> m_vm_lazy model = [] -> K [] ->
  (frm_zero (@fp_csr fx) -> msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs))) ->
  srealizes segs SCFG (mkCfg (@mkst fx' R' pc' M' (seg_rom segs)) model) K ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof.
  intros Hh Hl K0 Hms Hk. apply srz_fz; [exact K0|]. intros Z.
  exact (L5.cps_of_msteps segs fx fx' R pc M R' pc' M' model K Hh Hl (Hms Z) Hk).
Qed.

(* [comment removed for export] *)
Lemma with_frm (fx : FPState) R pc M model K :
  K [] -> (frm_zero (@fp_csr fx) -> srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
Proof. intros K0 H. apply srz_fz; [exact K0|]. intros Z. exact (H Z). Qed.

Variable A : pm_addrs.
Variable L : heap_layout.
(* [comment removed for export] *)
Definition strtod_spec_g (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (s endp n sp r : Z) (bs : list Z),
    PMSP.model_ok model -> K [] ->
    WDL.entry_scr A L R M sp r WDL.STRTOD_SCR ->
    getr R 10%bv = Z_to_bv 64 s -> getr R 11%bv = Z_to_bv 64 endp ->
    Z.of_nat (length bs) = n -> 1 <= n <= WDL.SNP_MAX -> (WDL.gnum bs = true \/ WDL.gspecial bs) -> L5.bytes_at segs M s (bs ++ [0]) ->
    sp <= s -> s + n + 1 <= hl_sptop L ->
    sp <= endp -> endp + 8 <= hl_sptop L -> L5.defined M endp 8 -> (endp + 8 <= s \/ s + n + 1 <= endp) ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> WDL.fregs_preserved fx fx' ->
        L5.u64_at segs M' endp (s + n) -> L5.bytes_at segs M' s (bs ++ [0]) ->
        WDL.mframe L sp WDL.STRTOD_SCR [(endp, 8)] M M' -> PMST.base_ok segs A M' ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

Theorem strtod_g_of (pc : Z) : WDL.strtod_spec segs A L pc -> strtod_spec_g pc.
Proof.
  intros H fx R M model K s endp n sp r bs MOK K0 ENT R10 R11 LEN N G BY S1 S2 E1 E2 DEF DJ BASE KONT.
  apply with_frm; [exact K0|]. intros Z.
  exact (H fx R M model K s endp n sp r bs MOK K0 ENT R10 R11 LEN N G BY Z S1 S2 E1 E2 DEF DJ BASE KONT).
Qed.
End G.
End FRMG.

End FrmGuard.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require HnIface.
Module NemSink.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require Import HnIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_NemSink () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List7existsbC47Corelib4Init5Logic8eq_ind_rc69OSSVerify5KrLib7Mh_01027NemSink4NESK6is_capC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_01027NemSink4NESK8cap_nextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7pow_1_rC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega5Tauto8GFormula04C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_01027NemSink4NESK4sp_BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK6sp_cszC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01c69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01027NemSink4NESK;sink_policy00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndi69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK<spo_B_nonnegC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK6sp_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_nmaxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK5spo_BC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05i69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Heap7HnIface4cszRC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoC46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6nle_gtC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC47Corelib4Init5Logic9False_indK46Stdlib9micromega=RingMicromega3Op206C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commc69OSSVerify5KrLib7Mh_01027NemSink4NESK4SP_TC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK;cszR_nonnegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK9cszR_monoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK<pow2_le_halfC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnIface4NREQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK7SP_T_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01027NemSink4NESK3PMEC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module NESK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record sink : Type := SK { sk_b : Z; sk_z : Z; sk_c : Z }.
Definition sink0 : sink := SK 0 0 0.
(* [comment removed for export] *)
Definition sink_own (k : sink) : list (Z * Z) := if sk_c k =? 0 then [] else [(sk_b k, sk_c k)].
(* [comment removed for export] *)
Definition is_cap (c : Z) : Prop := c = 0 \/ exists e, 0 <= e /\ c = 2 ^ e.
(* [comment removed for export] *)
Definition cap_next (c : Z) : Z := if c =? 0 then 1 else 2 * c.
(* [comment removed for export] *)
Definition sk_push (k : sink) (b' : Z) : sink :=
  if sk_z k <? sk_c k then SK (sk_b k) (sk_z k + 1) (sk_c k) else SK b' (sk_z k + 1) (cap_next (sk_c k)).

Lemma is_cap_next c : is_cap c -> is_cap (cap_next c).
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) [] "p'0h01Hh14__x1h27__arithh34__ffh48__varmaph55__with61ah71eh82Hah96__sat1h:1ch;6__sat0h<1xi001xh=1yh>1zh?2Heh@1bp;1p;2p;3p;4p;6p;5p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710g002`R0p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710g0051R1p4p710p8g005Oj13Tg006Oj1QTg0074j1MTg007Rj21Tg007oR2j27Tg008JR3j2>Tg008dj19Tg009fj2DTg00:Bj1OTg00:bj1NTg00;Bj1dTg00;`j1aTg00<>j1]Tg00<ij2BTg00=Lj2WTg00=nj2JTg00>Hj2VTg00?4j3:Tg00?Nj3TTg00?mj4STg00@_j4FTg00A:j4HTg00ATj3ITg00Anj28Tg00BKj25TP1j6<Tg00Bhj1ETg00CAj2PTg00Cbj2CTg00DJj3GTg00Dnj2RTg00ELj4;Tg00F7j1UTg00FYj2cTg00G<j6bTg00G`j4`Tg00H<j2LTg00HYj3_Tg00I<j3KTg00I_j1\Tg00J@j5[TP0j6ZTg00Jcj7YTg00KGj2^Tg00Kcj8XTg00LGR0f0R1g00LeR43:p=?1D41p=2f1R5=:01p=0P0P5g00MCP1C;p==P5g00MjR6g00NIR7P7g00NiR8P1g00OIFYp=4g00OiR9g00PIR:7:1p=A1^41p=6f3R;P6P7P7P8f2R<P5P1GXp=@%31g00Pi%?5R=%21R>g00QCR?#Q#MR@/11RA,0<'7X70,>0%9<#3P1%?<P0P4%91#3X:0RB%M?RC#?10CA,7>X70RD,>0P0PDP41D44RD11@4RE,0Cg00QhRF#ORG%NFRF%d0RH%a0RI%]0RJ1B04RK/=K'41WJ8RLP1P<g00RTRM,J91V1<=:9MdAT045CSRMb3b4b5PDP1b21J0ECFCH3IP9P01844PC15@4n0100000020000#3e%94#3eP;P1E<W0P1O110;A,7>X70,>0P3P0f4R3/0A,7>X70%93#3P1f6RE/0A,7>P2%25RDf7RN11@5'0f8RO#9#3P1%2;f:RP11@3'0P0f5RQ,1@RRPBP918R4RBP:P21851#A10<5#ER2[1051#E18<5#A[RS18;<#A\21P51P1n2001000000120000000X=0X<0PS^=0^<0P111@ERSP41C@ER2%6@RT%2N11@O#6[[RU1C@N%2Of9RO,1@RV#6RW[\T%2@RXg00S4RYAG@P5UW811@PRP#2\Y^8XP<P1PEO2X6T%6P^6TP3P1PNO2X6Tf;R3,1@#6^6TPGPF1R05RZPIPJPJP0PKg00SPR[1B0@R\C;,4J%U7R]P0PKP[1c0?R?C;,4JC@P]PJP6P7P7P8P0P?g00T7R8PKC;,4JEbC@PLPMb3b4b5X10%65\Tg00T^\=[^10P1f<,1@P5O2b2b0b9b;b9b0O3b0C`A:9:BP9P:P9P0P1PC11@NR:,5@R=n0100000020000#3X@915@SR7#?10=A,7>X70RA,>0P0PA1LECRA%2A11@ARA,07PGPFPZPIPJ1=K?,4JR7P]1B0CR69_0?,=K,4JC@PLPMb3b4b5X101L5C#2\>^10P1PNP;O2R;b2P011@CRN,5S10=1X>0P0P@15:1,0=X>0P2PUAG@O5VYX8X%2V\Y^8XP<P1PQO2X6TPW^6TPGPFPZPIP0AK0\?P8AK0?\C;,4JPLPMb3b4b5X1015@1151@'0^10P1PPO1b2b9b;b9PN%\@E<PAP@PEPCPGPFPZPIPJP7P]P7C@PLPMb3b4b5X10PD\>^10P;b2PGPFPHPI1=K6,4JPLPMb3b4b5%2CP1b2D[E<CFCH3I18S4P1EZb0P9P0PBPC15@Rn0100000020000#3e%9R#3eP3P1E<W0W?P5P1O2n2001000000121000000W0X70P5P1O2n2001000000121100000W0P1O1n200100000021000011000W0X:0P1O1X:0o"). Qed.
Lemma cap_next_pos c : 0 <= c -> 0 < cap_next c.
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) [] "p'0h01Eh17__arithh24__ffh38__varmaph45__with54__x1h61ch71xh81yh91Hh:1bi001bp;2p;3p;1p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g00Anj21Tg00=nj2<Tg00?4j30Tg009fj26Tg0074j1=Tg006Oj1VTg00BKj2;Tg00KGj23Tg00:Bj1CTg00:bj1BTg00;Bj1ATg00;`j1?Tg00<>j1>Tg00<ij28Tg00ELj45Tg00=Lj2UTg00>Hj2TTg00?Nj3STg00?mj4LTg00Bhj14Tg00CAj2ETg00U;j2DTg00Udj1FTg00VCj2:Tg00Vlj3GTg00WUj3HTg00X>j2ITg00Xjj3JTg00Dnj2KTg00FYj2@Tg00F7j1MTg00G<j6NTg00I<j3OTg008dj1PTg00Jcj7QTg00Kcj8RTf1R0g00MjR1g00NIR2P2g00NiR3f0R4g00OIFQp=2g00OiR5g00PI704p=7f3R6P1P2P2P3f2R7P0P4GRp=9g00LGR8g00LeR9,14P51<541109=054P51169=054f4R:,69P5P8P7g00QCR;#=R<%V;#=R=f5R>';n0100000020000,39[]0P01179R?g00RTR@5051696g00QhRA#CRB%BARC%A8%?8RD%>8REP81889RFg00SPRG188<C5'21UE3RHP4P71<5@1T47=05@dAS890CLR@b2b3b4139<P4b1UW0%7?g007o1104#7A0870#4[R?A0804#41170#7R<[A0867#4\<1E04P0n2001000000120000000X88X78P?^88^78P4P:P9P0O3A08:9#4169>1D8=g00YJR>#F,:85G81:8>5H8g00Yi'I=JABPC1K80PDPEP8PFg00MC1@8;R;C5,2E%M2RDPEPEP1P2P2P3P8P;g00T7PFC5,2EENPDP8PFPG188==O8;C5,2EC9C9PHP@b2b3b4X581694R@A0809g00T^[1;=7,39[[^58P4f7P0P7O3b1Ub0b9W0n0110000020001P4O1b0b:%P0,39\@eX68P4O1W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record sink_policy : Type := SP {
  sp_mode : Prop;          (* [comment removed for export] *)
  sp_cap : Z -> Prop;      (* [comment removed for export] *)
  sp_nmax : Z;             (* [comment removed for export] *)
  sp_csz : Z -> Z;         (* [comment removed for export] *)
  sp_B : Z;                (* [comment removed for export] *)
  sp_hb : Z -> Prop        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition sink_pot (P : sink_policy) (c : Z) : credit :=
  (if c =? 0 then 2 else 1, sp_B P - (if c =? 0 then 0 else sp_csz P c)).

(* [comment removed for export] *)
Record sink_policy_ok (P : sink_policy) : Prop := SPO {
  spo_csz_nonneg : forall c, 0 <= sp_csz P c;
  spo_B : forall c, is_cap c -> 0 < c <= sp_nmax P -> sp_cap P c -> sp_csz P c <= sp_B P;
  spo_hb_mono : forall h h', sp_hb P h -> h' <= h -> sp_hb P h';
  (* [comment removed for export] *)
  spo_next : forall c h, is_cap c -> (0 < c -> sp_cap P c) -> sp_hb P h -> c <= h ->
             0 < cap_next c <= sp_nmax P
             /\ (if c =? 0 then 0 else sp_csz P c) + sp_csz P (cap_next c) <= sp_B P;
  spo_nmax : sp_nmax P <= NREQ;
  spo_B_nonneg : 0 <= sp_B P          (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithImage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.

Definition sink_at (P : sink_policy) (M : word -> option byte) (o : Z) (k : sink) : Prop :=
  L5.u64_at segs M o (sk_b k) /\ L5.u64_at segs M (o + 8) (sk_b k + sk_z k) /\ L5.u64_at segs M (o + 16) (sk_b k + sk_c k)
  /\ L5.defined M o 24 /\ acc M o 24
  /\ 0 <= sk_z k <= sk_c k /\ is_cap (sk_c k)
  /\ (sk_c k = 0 -> sk_b k = 0)
  /\ (0 < sk_c k ->
        L5.defined M (sk_b k) (sk_c k) /\ acc M (sk_b k) (sk_z k) /\ ann M (sk_b k) (sk_z k) (sk_c k)
        /\ block_range L (sk_b k) (sk_c k) /\ sp_cap P (sk_c k)
        /\ sk_c k <= sp_nmax P).                  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sink_pot_fst P c : 1 <= fst (sink_pot P c).
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["WithImage"] "p'0h01ah13annh23acch31Ph47__arithh54__ffh68__varmaph75__with81ch91bi001bp;2p;1p;4p;3p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0g001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g00Anj2KTg0074j18Tg006Oj10Tg009fj21Tg00ZUj12Tg00[3j16Tg00[Vj1?Tg00:Bj1>Tg00:bj1<Tg00;Bj1;Tg00;`j1:Tg00<>j19Tg00<ij24Tg00ELj47Tg00=Lj2JTg00=nj2ITg00>Hj2HTg00?4j3ETg00?Nj3@Tg00?mj4ATg00\8j1BTg00]6j2=Tg00^6j2CTg00^Sj4DTP1j33Tg00_3j2FTg00Jcj7GTf1R1g00Mjg00NIR0P0g00NiR0f0R2g00OIFGp=5g00`5R3g00LGR4g00LeR5,K2R6g00OiR7P7g00QCR8#8R9P7P4P2%08R8#8R:P9n0100000020000'1P2%08#0R8#0#0#0#2#6%28#6#?[R8p,3annP2f2R;O2W0R<p-0R=\4R>\4^08R?P1P2f3O2X08R@P>^08R>P1P2f4O2X08RAP=^08R=p,3accP2f5O2X08RBP>P1P2f6O2X08R8P=g00QhRC#>RD%<CRC%;4RE%:4RF%94RGP41449RHg00MCRI144:C7'51JG0R0P2P;g00RTRJ,I71H2;=E7JdA@451CARJb5b6b7119:P2b4b2b2b1b1b1P<P?P@P>PAP=PBP>P8P=PDPCPEPFP4PHPIPHC7,5GP0PJb5b6b71199P2b4b2b2b1b1b1n0110000020101b9P4P4P7P4P6P:P9n0100000020000%B1P7P4P6P51=12n0100000020000'CCD9344,19e1F129344,19eX84X33P1P2O2W8W3o"). Qed.
Lemma sink_pot_nonneg P M o k : sink_policy_ok P -> sink_at P M o k -> 0 <= snd (sink_pot P (sk_c k)).
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["WithImage"] "p'0h01Hh14__x1h24__x2h33EQ0h47__arithh54__ffh68__varmaph75__with83HBKh91Mh:1Ph;2_Hh<3_H0h=3_H1h>3_H2h?4__p1h@4__p2hA4__p3hB4__p4hC4__p5hD4__x3hE1khF1ohG1xhH1yhI2B0hJ3CAPhK2H0hL2HchM3Hc0hN2HphO2HzhP2NMhQ2POhR3_H3hS1ahT1bi001bp&0p;1p;4p;3p;2p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0g00a<R1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g006Oj1ATg00ZUj1gTg00[3j1dTg00[Vj1mTg00aYk105Tg00bcj4|Tg00cdj11Tg00dbj4TTg0074j1OTg00e_j12Tg00f]j10Tg00g[j1jTg00h@j3BTg009fj26Tg005Oj1WTg007oR0j25Tg00i>j2nTg00\8j1:Tg00Anj2GTg00=nj2[Tg00?4j3@Tg00]6j2?Tg00:Bj1lTg00:bj1kTg00Dnj2STg00;`j1iTg00<>j1hTg00<ik204Tg00FYj2ZTg00F7k103Tg00jDj3eTg00=Lk202Tg00>Hk201Tg00?Nj3{Tg00?mj4zTg00Bhj1QTg00CAj2yTg00Udj1YTg00VCj2XTg00WUj3aTg00X>j2xTg00Xjj3wTg00;Bj1vTg00jgj4UTg00ELj4LTg00kEj3ETg00lGj2MTg00mGj1RTg00nHj6uTg00^6j2`Tg00^Sj4tTg00H<j2bTg00KGj2rTg00_3j2qTP1j3fTg00Jcj7pTg00Kcj8}Tg00G<j6oTg00oGj6~Tg00okk700Tf5R1f4R2f3R3f2R4'bf1R5f0R6'bCTp=;g00LeR7/641656'5p=Kg00LGR8?@67p=31r76p=8f6R9?E121M34%R6,65'5'5p=7AB1231556,54'5p=4%W41556'5p=91556,54p=C1q569f88,67p=>1674/55/56,53p=P1676p=F1545/56p=c1`56,67p=DP8P5g00MCP6CLp=JP5g00MjR:g00NIR;P;g00NiR<P6g00OIFpp==P3P:P;P;P<P4P5P6G}p=<g00OiR=g00PI7@6p=VP5P:P;P;P<P6Eop=_1M34%R6,65'5p=IAE345/56,52,51p=^%R6,65p=]P5P:P;P;P<P6E~p=NP4P:P;P;P<P5P6K00p=H1656,54p=\Af886,67p=sg00`5R:g00QCR>#AR?#AR@#ARA#ARB#A#A#g#d%gA#d#m[RCg010ORD&053P2P3P4P5C|P0p,4segsREP2P3%14RFCTPEP2P3%OARAPF%24RGE;PEP2P3%OBRBPF%04RFE;P2P3%j>#A#A#A#ORHp,3accRIP2P3PHO3AKGGF%3F%13RG#3[%8FP1PG%03RJPIP1PG%23RKO3p,3annRLP1PGPKPJO4p,1LRKPGPJP9PJPJP9F7E4[59FE43C1>9JP6PEP9P1%12CTPEf7RJP9PA%11RF%21RGE;PEPJP9PBPF%01RFE;PJP9PHPIPJP9PHO3AKGGF%3F%19RG#3[%8Ff8RMPG%09RNPIPMPG%29ROO3PLPMPGPOPNO4PKPGPNf9RPPNPNPPF7E4[59FE43CP0PEPMPJPAPGPOE;PEPMPJPBPGPNE;ABMJHPIPMPJPHO3PO16ON%3N%1JRO#3[%8NPPPO%0JRGPIPPPO%2JRFO3PLPPPOPFPGO4PKPOPGf:ROPGPGPOF7E4[59NCP3C1>OGP6PEPOPPPA%1M%2ME;PEf;RAPOPB%1P%0PRGE;ABAOHPIPAPOPHO3%2PRP16PG%3G%1ORP#3[%8Gf<RNPP%0ORFPIPNPP%2OROO3PLPNPPPOPFO4PKPPPFf=RQPFPFPQF7E4[59GCP3CP0PEPNPAPBPPPFE;PNPAPHPIPNPAPHO3AKOOF%3F%1ARO#3[%8FPQPO%0ARPPIPQPO%2ARAO3PLPQPOPAPPO4PKPOPPf>ROPPPPPOF7E4[59FE41>OPP6PEPOPQPB%1N%0NE;f?RNPOPHPIPNPOPHO3%2QRB%0QRQ7KB%3Q%1ORB#3[%8Qf@REPB%0ORPPIPEPB%2OROO3PLPEPBPOPPO4PKPBPPfARBPPPPPBF7E4[59QE4P0ABENHPIPEPNPHO3PO16OP%3P%1NRO#3[%8PPBPO%0NREPIPBPO%2NRQO3PLPBPOPQPEO4PKPOPEfBROPEPEPOF7E4[59PCP1>OEP6ABOBHPIfCREPOPHO3%2BRP%0BRB,6P%3B%1ORP#3[%8BfDRQPP%0ORFPIPQPP%2OROO3PLPQPPPOPFO4PKPPPFfERPPFPFPPF7E4[59BCPP0PIPQPEPHO3%FO16OF%3F%1ERO#3[%8FPPPO%0ERQPIPPPO%2EREO3PLPPPOPEPQO4PKPOPQfFROPQPQPOF7E4[59F3c1>OQP6PIPOPPPHO3%2PRH#F%0PRQ,6H%3Q%1ORH#3[%8QfHRFPH%0OREPIPFPH%2ORBO3PLPFPHPBPEO4PKPHPEfIRHPEPEPHF7E4[59Q3cP0AKBBE%3EfGRB#1RQ#3[%8EPHPQ%0BRAPIPHPQ%2BRGO3PLPHPQPGPAO4PKPQPAfJRQPAPAPQF7E4[59E1>QAP6%2FRA%0F7KA%0HRA%3A%1QRE#3[%8AfLRAPE%0QRGPIPAPE%2QRQO3PLPAPEPQPGO4PKPEPGfMREPGPGPEF7E4[39P0%WG%3GfKRQ#1RR#3[%8GPEPR%0QRGPIPEPR%2QRQO3PLPEPRPQPGO4PKPRPGfNRRPGPGPRF7E4['51>RGP6%0A#W%0ERG#3%1RRQ#3[%8GfPRGPQ%0RRSPIPGPQ%2RRRO3PLPGPQPRPSO4PKPQPSfQRQPSPSPQF7E4['5P0%3SfORR#1RT#3[%8SPQPT%0RRSPIPQPT%2RRRO3PLPQPTPRPSO4PKPTPSfRRTPSPSPTF7E4[1>TSP6%0G#3%1Q#3[%0Q#8fTRG%1TRS%0TRRPIPGPS%2TRTO3PLPGPSPTPRO4PKPSPRfURSPRPRPSF7E4[1nSQ%:S#FfS#0RR/G7RTP=1[=6%0G/G7=@=6P=fVRG#0/G7=@=6fZRU#:RVP=P8P5P7fW#0RW,?Un0100000020000'D]3P5%0S/G7RSg00RTRX5@=g00QhRY#lRZ%kYR[1S85%i8R\%h8R]20487R^1Z8>R_'J,=]&03;R;Ae8_^,J^,=]C<202]<R<P6P41[=X20164=@=XdA{875CzRXb5b6b7X18%F61D57[^18P6PVP2O2b4W3%VSP01G56#VA@845#Q[RSA@856#Q1G45#VRV[A@834#Q\V1y56P5n2001000000120000000XH8XG8PS^H8^G8P6PWP7P5O3%3W#QP0fXRW#2RS#F%0WRW,6SfYRS#0RV#8PN%2URN#Ff[R`#2%0`Ra'6g00YJ#YRb#YRc#Y,X81X8c1X8b5a85a8g00Yi'x=wYZP[P81S84P5%v8RYCURbP\P]P8P_g00T7RcP^CL,=],_]RdP;P]1Z8?Re/J_,=]RfP;P]1J^e,=]P;P8P^g00SPRgP_CL,=]RhC<C<C<P<PXb5b6b7X18X28%36g00T^Ri[1645%F3%83Rj[[[^18^28P6f]Rk#2Rl%0kRmP1P5P4O5b4WKW0P5P6O2n2001000000120000000%8WPJP6O1P`%1SRWPVPIP`PW%2SRSO3PLP`PWPSPVO4PKPWPVf\RWPVPVPWF7E4P0%1URV%0URU5BWPIPWPVPNO3PLPWPVPNPUO4PKPVPUPkPUPUPkCIE^f^RU#:1?Ua'DP6%1W%0W5BUPIf_RW%1kRkPlO3PLPWPkPlPmO4PKPkPmf`RkPmPmPkCIE^P0PIPk%1URm%2URlO3PLPkPmPl%0URUO4AEKmUfaRmPUPUPmCI3CfbRU#:%0W,?U'DP6PIPU%1k%2kO3PLfcRk%1mRW%2m%0mRmO4AEKWmfdRWPmPmPWCI3CP0PLPW%1URm%2U%0URUO4PKPmPUfeRmPUPUPmF7ffRU#:%0k,?U'DP6PLPU%1W%2W%0WO4PK%1m%0mRmfhRWPmPmPWF7P0%1U%0URU5EKfiRmPUPUPmCIfjRU#:fg#0,?U'DP6%1W%0W5EKflRW%0mRmPmPWCIP0fmR0%0URU'M1]U0fnRU#:fk#0,?U'DP6foRm%0W'M%00fpRW']fqRkP0%0UR0PQPAPPO1PW%1URPP0PIPWPP%2URUO3PLPWPPPUP0O4PKPPP0PkP0P0PkF7E4p-0RPPZP[PbP\P]PhP;P]PdP;P]1N]21N]11N]91N]J1N]M1J_e,=]Rd5H]5H]5H]5H]5H]P;AH]hdC<C<C<P<PXb5b6b7X18X28X?PX@PXAPXBPWC%86%35Pi[A\M439C9J9C21A\j32[[[^18^28^?P^@P^AP^BP^CPP6fsRP%0WR1'M%1WRJ=EK1PLfrR9PJ%2WRWP1O4PIP9PJPWO3AB9J1%RPP1PBPFP5O:b4b8P5Eu1?k0%:k'6PEPOO1Pk%1mRO%0mREPIPkPO%2mRmO3PLPkPOPmPEO4PKPOPEP9PEPEP9F7E4PZP[P8P81S83P4PYCUP5PYCUP\P]PfP;P]P8P^Pg1Z8@R@CL,=]P;P]P8P@PcP^CL,=],_]P;Ae8_e,J^,=]C<C<C<P<PXb5b6b7X18X28XD81656%32Pi[1D32[\j[^18^28^D8P6%0kRkftRj/?k%:jP4PFPHO6b4b8b0WPWJP5P6O2n2001000000121000000W0W>P5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000W0W<P5P6O2n2001000000121000000W0W;P5P6O2n2001000000121000000bSbNb3b0W3n0110000020001P6O1b3bTP8P8P=P8PT%O?%O>n0100000020000%:GP=P8PTP71?GRn0100000020000'`Ct#se1>GRebIW8WMP5P6O2n2001000000121000000W0WLP5P6O2n2001000000121000000W0WOP5P6O2n2001000000121000000W0WRP5P6O2n2001000000121000000W0W>P5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000W0W<P5P6O2n2001000000121000000W0W;P5P6O2n2001000000121000000W0WQXEDXF8X9CX::P3P4P5P6O4WEXF8W9W:o"). Qed.

(* [comment removed for export] *)
Definition o_sink (fb : Z) : Z := fb + ne_off_sink E.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition push_back_spec (P : sink_policy) : Prop :=
  sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (o pv sp r : Z) (k : sink),
    hi_heap HI (sink_own k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 pv ->
    sink_at P M o k ->
    sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    sp <= pv -> pv + 1 <= hl_sptop L -> (pv + 1 <= o \/ o + 24 <= pv) -> L5.defined M pv 1 ->
    (sk_z k = sk_c k -> 0 < cap_next (sk_c k) <= sp_nmax P
                        /\ (if sk_c k =? 0 then 0 else sp_csz P (sk_c k)) + sp_csz P (cap_next (sk_c k)) <= sp_B P) ->
    PMSP.credit_le (sink_pot P (sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        sink_at P M' o (sk_push k b') ->
        L5C.hpres L LBX sp (PMSP.pm_scr 0) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (sink_pot P (sk_c k)) (sink_pot P (sk_c (sk_push k b'))) ->
        model_but_vm model model' -> hi_heap HI (sink_own (sk_push k b') ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (ne_push_back E) M model) K.

(* [comment removed for export] *)
Definition push_back_ind_spec (pc : Z) (P : sink_policy) : Prop :=
  sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (q rr o pv sp r : Z) (k : sink),
    hi_heap HI (sink_own k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    PMSP.entry A L R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 q -> getr R 11%bv = Z_to_bv 64 pv ->
    L5.u64_at segs M q rr -> rr mod 8 = 0 -> 0 < rr -> L5.u64_at segs M rr o -> 0 < o ->
    sp <= q -> q + 8 <= hl_sptop L -> sp <= rr -> rr + 8 <= hl_sptop L ->
    sink_at P M o k ->
    sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    sp <= pv -> pv + 1 <= hl_sptop L -> L5.defined M pv 1 ->
    (sk_z k = sk_c k -> 0 < cap_next (sk_c k) <= sp_nmax P
                        /\ (if sk_c k =? 0 then 0 else sp_csz P (sk_c k)) + sp_csz P (cap_next (sk_c k)) <= sp_B P) ->
    PMSP.credit_le (sink_pot P (sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        sink_at P M' o (sk_push k b') ->
        L5C.hpres L LBX sp (PMSP.pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (sink_pot P (sk_c k)) (sink_pot P (sk_c (sk_push k b'))) ->
        model_but_vm model model' -> hi_heap HI (sink_own (sk_push k b') ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
End WithImage.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Policies.
Context {bmK : BMode}.
(* [comment removed for export] *)
Definition SP_T (zmax hb : Z) : sink_policy := SP True (fun _ => True) zmax cszR (cszR (zmax / 2) + cszR zmax) (fun h => h <= hb).

Lemma cszR_nonneg n : 0 <= cszR n.
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["Policies"] "h02Hah14__p1h24__p2h34__x1h44__x2h54__x3h64__x4h71nh81Hh92H0h:2H1h;2H2h<2H3h=2H4h>7__arithh?4__ffh@6__sat1hA6__sat2hB6__sat3hC8__varmaphD5__withE1qhF1rhG2z0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g006Oj1?Tg0074j1ETg00g[j1>Tg007Rj2uTg011Oj2<Tg00BKj26Tg011lj2ZTg00KGj22Tg012Nj2LTg007oj25Tg009fj2DTg00Pij2QTg00Cbj2mTg00DJj3fTg012kj2dTg013\j2bTg00?4j3BTg00Bhj1`Tg014=j29Tg00H<j2@Tg014]j2]Tg015Dj2\Tg015kj2[Tg016Qj2YTg0177j1XTg017Uj2WTg00Udj1FTg00VCj2HTg0186j3VTg00WUj3KTg00X>j2OTg018_j2PTg00:Bj1UTg00Xjj3JTg00:bj1TTg00Dnj2STg00;Bj1tTg00jgj4RTg00;`j1sTg00<>j1rTg00<ij28Tg00ELj4:Tg00F7j1pTg00FYj2ATg00G<j6lTg00HYj3GTg00I<j3MTg00ZUj1eTg019Kj3cTg019nj7gTg00=Lj2hTg00=nj2iTg00>Hj2jTg00?Nj3kTg00?mj4aTg01:Rj1nTg00Jcj7oTg00oGj6_Tg00okj7^Tg00Kcj8qTf0R0#?#?p=7%>0#>p==f2R1f1R2'@/@0p=0g00LGR3?B20p=4g00LeR4/D0p=1P2g00MjR5g00NIR6P6g00NiR7P0g00OIFop=3P2P5P6P6P7P0E_p=NP1P5P6P6P7P2P0F^p=If3R8P5P6P6P7P1P2P0Gqp=;P3P2g00T7P0C:p=Cg00QCR9#?R:#ER;%>:#7R<#ER='uR>%>9R?#=#=#=#=#=#ER@900=%?:RA#7#7#7#7#7#ERB'</6BRC'Z12>C1L>CRD/4C'51DC>14D>'5'QA02=@/<B/6B,L>P31m;=124;%1=124>[[%1;RDg00S4RCAf;=2UW0%1>\C^0Df4RD?0=@RC/dB%1C%1Bf6RE?0=@RF/<BRG#1[[f5RH?0=@/bBAB3B4RI#`16BG19FB'@,4F[1]FB124BRFf7RG?0=@RJ/9BRK#112KB'5[1\JB12B4f8?0=@RJ/9BRK,2B1DK4'5[1[JBf9?0=@RJ/<B=B34\I1YJBf:?0=@RJ/9B/4J\I1<JBP3f;RJ?0=@/9BP3p-0RKg00QhRL%X9,W3g00YJRM#FRN,H3RO5V31H3MRM5K3RPg00YiRQ'O%FN#F,H3AK3OM/OQ'P,PP%UL5JL3J%TLP3P31S3DP1%t3CRP21S38CR%s3%r3RLPLP31834RPg00SPRQ183BRMC:,3L%p6ROP3PPg00MCRN1A3ARAC:,3L1NLE5ILC;POPLPLPLP5P6P6P71CMP,3LElPO1A3?183=5G3183@5G31A3:R:9M3M=G3A'C,3LC;POPLPLP5P6P6P7P3183;%e<5c3R<PQAM3:MR:C:,3L1A39R9/C:,3L5IL1NLG1C9<,3L5ILFgPOP3PPPNP9C:,3LC;C;C;1hL7P0P1g00OiRLg00RTR7'i1j01=BL7dAk342Cab?bCbDX33X43X53X63X1KW2%1D/5H\Fg00T^\I16B8/@H,4C[168BRC,2>141C'5141>,5G'Q%18[[[^33^43^53^63^1K^2KP0161B/D>122BP2f=P1PJPEPGf<O9b>bFbEb=b<b;b:b8b@bAbBbGb9%n0#1eX73P0O1X73o"). Qed.
Lemma cszR_mono n m : n <= m -> cszR n <= cszR m.
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["Policies"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with62Hah74__p1h84__p2h94__p3h:4__x3h;4__x4h<4__x5h=4__x6h>4__x7h?4__x8h@1mhA1nhB1HhC2H0hD2H1hE3H10hF3H11hG3H12hH2H2hI2H3hJ2H4hK2H5hL2H6hM2H7hN2H8hO2H9hP6__sat3hQ6__sat4hR6__sat5hS6__sat6hT1qhU2q0hV1rhW2r0hX2z1hY2z2p&0p;2p;1p;3p;4p;5p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g009fj21Tg006Oj1?Tg00g[j1ATg0074j1TTg00:Bj1qTg00:bj1nTg00;Bj1jTg00;`j1hTg00<>j1fTg00<ij2KTg00=Lk200Tg00=nj2zTg00>Hj2yTg00?4j3RTg00?Nj3uTg00?mj4tTg00KGj22Tg00Dnj2LTg00jgj4JTg00FYj2\Tg00F7j1kTg01;Hj5iTg011Oj24Tg007Rj2gTg00BKj25Tg011lj2[Tg012Nj2NTg00Pij2MTg00Cbj2eTg00DJk303Tg012kk202Tg013\j2dTg00Bhk101Tg014=j29Tg00H<j2ETg014]j2cTg007oj2<Tg015Dj2bTg015kj2aTg016Qj2_Tg00Udj1FTg00VCj2GTg0177j1xTg017Uj2wTg0186j3vTg00X>j2QTg018_j2OTg00U;j2sTg00Vlj3]Tg00G<j6pTg00I<j3PTg00ZUj1oTg019Kj3rTg01:Rj1ZTg00ELj4UTg00Jcj7^Tg00HYj3mTg00Kcj8XTg00WUj3{Tg00Xjj3lTg00oGj6|Tg00okj7}Tg019nj7~Tf0R0#?#?p=H%A0#Ap=Sf2R1f1R2'E/E0p=0g00LGR3P2g00SPP0CUp=YP2g00MjR4g00NIR5P5g00NiR6P0g00OIR7F^p=71\30p=>P1P4P5P5P6P3P2g00MCP0CUP7F^p=8Am320p=6f3R7P4P5P5P6P1P2P0GXp=@AR320,<1p=;g00LeR8/10p=3AR308p=WAR320p=DA{320p=Cg00QhR9?l20p=:P2P4P5P5P6P0E|p=VP1P4P5P5P6P2P0F}p=BP3P2g00T7P0CUp==f6R:P4P5P5P6f5R;f4R<P7P4P5P5P6P1P2P0GXGXp=IP1P4P5P5P6P2P0F~p=`1120g00QCR=#?R>#AR?#HR@#TRA%A=RB#ARC#A#S#S#S#S#TRD501REA02ADRF%?>RG#?RH#?#H#H#H#H#TRI%q9RJ%n9R9%j3RK%h3RL%f3RM1K38RN1K3IRO'Y'7RP200M6RQP0P1g00OiRRg00RTRS'z1y01=RRSdAu382CtRSb3b4b5128IRRP0b2PJP9P31L31P2PKCJPLPM1\3=RT%>>RU58MRV%k5RW1K3ARX,6T1K3DRY'616UX/6Y58MC@PQPSb3b4b5X03X13110211FE[^03^13P0P1P7P2O3b2Di14EIRE14FI'1%T>R>/gARF15EIRE'[12FE1NFERZ;;E11EF?;ZF'MA07AD/4I/5I,NFP3A0;AD/4I/5IRZ,[F12FZ1NFZRE;;Z11ZF?;EF'MA0:ADRE/4I/5I,NFP31e>A128>%3A128F[[%3>RZg00S4R[B03>A2UW6%3F\[^6Zf9RZ?0ADR[002IR\%3[%3IR[f;R]?0ADR^/4IR_#3[[R`P\P`f:R`?0AD/dI%WIR\$01Ra15I_19^I'E,D^[1c^If<R^?0ADR_/9IRb#312bI'<\R1b_I12I8R_f=Rb?0ADRc/9IRd,2I11d8'<[1acIf>Rc?0ADRd/4I#W\\1_dIf?Rd?0ADRe/9I/De\\14eIP3f@Re?0AD/9IP3fB?0AD/dIfCRf?0ADRg14gI,5I19gI'E'D\a1cgIfDRg?0ADRa/9IRh#312hI'<\R1baIfERa?0ADRh/9IRi,2I11i8'<\_1ahIfFRh?0ADR_/4I#W\\1__IfGR_?0ADRi/9I/Di\\14iIP3fHRi?0AD/9IP3p-0R8g00YJRj#FRk#F#FRl#F#FRm,G3Rn%x=,w31G3lRl5v31G3jRj'C'CR=g00YiRo'QRp1G3k/Cj/Qo,On,O=Rk1Cjl/Qo,O=R=%Fm,G31s3IRm=]3jA]3ml,Cn'C/Qo'ORo1:pJ,:k,:=,:o':':':':P9P3P3P3f8R9,L3P<PKCJP11L3:CJP2P31L3;P7f7R7,L3CJCJPLPMPMPPPW%>HRH98MN1VM`5BMC@PWPMPMPMP4P5P5P61=ON,7MEpR6PW%>BR5/6X/6YR4%>?R?9P3O/6H'=,7MC@PWPMPMPPPW%>CRC98MN1VM]5BMC@PWPMPMP6PW%>GRG/6X/6Y%?B#>RB9P3O/6C'=,7MC@PWPMPMA8MN4PWPMA8MNOPWA8MN?FIPWPM1K3>%o@5r3R@AP3?OR>'Y,7M1=T>,7M5BM1VM^1=T@,7M5BM5`MPWPMAP3BORO,Y@,7M1=UO,7M5BMA8MO@1=U@,7M5BM5`MPWPMA8M?BPWPMA8M5GPWPVC@FIFIFIFIPQPSb3b4b5X03X13X:3X;3X<3X=3X>3X?3X78X88W9%39/<Z\Rg00T^\\R\A0<AD15I:/EZ'D[%3Z/<^\RA07AD15IZ/E`'D\\%3E%3`\[[15ZIR[,2F?;;[A;d;F'M15]IRd,2F?;7d11dF?;7F'M11]^11`]11Z`[[[[[[[[[^03^13^:3^;3^<3^=3^>3^?3^78^88^98P0151I/1F129I122IP2P9PZP1fIfJPaPfP:P7PbPcPePgPhP_PiODb2bWbUbGbFbEbObNbVbTbMbLbKbJbIbPbQbRbSbYbHbXbDbC%Z1%Z2'1eWBX@3XA3P2P0O2X@3XA3o"). Qed.
Lemma pow2_le_half e j : 0 <= e -> 0 <= j -> 2 ^ e < 2 ^ (j + 1) -> 2 ^ e <= 2 ^ j.
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["Policies"] "p'0h02Hah11ah26__sat1h36__sat5h46__sat2h54__x1h64__x2h76__sat3h86__sat4h97__arithh:4__ffh;4__p1h<6__sat0h=8__varmaph>5__with?1Hh@2HchA6__sat6hB1ehC1jhD1mhE1nhF2H0hG2HehH3HgthI2HjhJ3HlehK3HlthL1si001si011gi021lp;1p;2p;3p;4p;5p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g006Oj1FTg0074j1ETg007Rj20Tg00H<j24Tg00KGj28Tg01;mj2RTg009fj23Tg01<Tj2;Tg01=0R0j2KTg00Bhj1=Tg01=Pj2ITg00Cbj25Tg00DJj36Tg00:Bj1WTg00:bj1VTg00;Bj1UTg00;`j1TTg00<>j1QTg00<ij2>Tg00=Lj2PTg00=nj2OTg00>Hj2NTg00?4j3MTg00?Nj3LTg00?mj4JTg01>0j5CTg00Dnj2DTg00jgj4<Tg00g[j1BTg00FYj29Tg00F7j1HTg00ELj4@Tg00oGj6GTg00HYj3STg01>Wj2ZTg00Jcj7YTg00Kcj8XTg00LeR1f0R2'3p=11812p=2g00LGR3f1R4g00SPP2C@p=?P4g00MjR5g00NIR6P6g00NiR7P2g00OIFYp=7P3P4g00MCP2C@p=Af3R8P5P6P6P7f2R9P4P2GXp=:%14R:g00QCR;#FR<#ER=/08R>%E;R?,49,0='8f4R@,0=RA/R>13A>1;A>'KP0f5,0=R0/3A1;0Af6RA,0=R>/30RBP2P2XJBP2O11;>0f7R0,0=/3>g007o1342R>#=1849RB[RC1824RD1394#=RE[1898\E1I42P4n2001000000120000000XD3XE3PC^D3^E3P2f8RCP013C0REP=f9R8PC15=8RF%2=RGf:RH#1f;RI,0=RJ#2[[RK%1=RLg00S4RMf<RN=6=4UW0RO10=NRP#1\M^0LRQ14H?RR,5=RS14I?RT#114N?RU,0=RV#2[\GRWf=RX/4?RY=6=4VMX0LRZ10=YRY#1\M^0LR[15=NR\%1Xf>R],0=R^#2R_[\GR`f?Ra=6=4VMX0LRb10=aRc#1\M^0LRdP9P2PXO2X1GRe%2cRc^1GRfP0P2PaO2X1GRafARg,0=#2^1GRhg00QhRi#WRj%ViRi%U3Rk%T3Rl%Q3Rm1>311>3='?'71Pm7RnP2P9g00OiRog00RTRp'O1N29=MopdAL314CJR1b:b=b>PGP2b9Rpb3b2b<b2b4b7b8b3P2DC10=810=CRo'315=H%1I%2P[\GA6=X4VMX0L10=XRP#1\M^0L15=T%1U%2Y[\G14]?RY=6=4VMX0L10=Y#1\M^0L15=X%1]Pc[\Gf@Rc=6=4VMX0L10=cRX#1\M^0LP9P2P]O2X1G%2X^1GRXP0P2PcO2X1GfB,0=RY#2^1Gp-0RqPjPiP3PkP9P31D39RrP4PkC<RsC<PlPm%B;,93Rt%B<,93Ru'A,7m%H6RvPmP3Ptg01?6PuC@,7mPvPmP5P6P6P7P@EGR7C:C:PnP1b:b=b>X53X63W;13241;49P@[[^53^63^;qP2g00T^R6PYfC,0=P8PNO5b9b3b2b<b2b4b7b8b3b@W@%=EeO3b?18A0P=140?RAPC15=CRC%1810=H#2[\GRHA6=I4VMX0LRE%1J\M^0LRJ148?,5=R5%1R10=T#2[\GRTA6=U4VMX0LRU%1V\M^0LRV15=IRI%1N%2P[\GRPA6=]4VMX0LRR%1^\M^0LRLP9P2PNO2X1GRNP_^1GR_P0P2P]O2X1GRGPXPpb3b2b<b2b4b7b8b3PCPHPEPJP5PTPUPVPIPPPRPLPNP_PGPXPjPiPsPlPm193;R;193<Rs'?,7mPv1>3?9S3;/As,7mC:PnP1b:b=b>X53X63144?/39\D^53^63P2PgPcP8O3b9b3b2b<b2b4b7b8b3DC10=A/3oPFPKPOPQPSPWPZP[P\P`PbPdPePfPaPhPjPiP3P3PrP9PkC<P91D34C<PlPm%F<,93R</At,7mPvPm1?t<,7mPvP7C:C:PnP1b:b=b>X53X63X;qP@\B\>^53^63^;qP2P614g?,0=PYP8P]O5b9bAb4b2b4b7b8b3bAbFb?'ZWHP2O1n200110000021010211101bLWKXI:WGXC3XB3P4P2O2XC3XB3o"). Qed.

(* [comment removed for export] *)
Lemma SP_T_ok j hb : 20 <= j -> 2 * 2 ^ j <= NREQ -> hb < 2 * 2 ^ j -> sink_policy_ok (SP_T (2 * 2 ^ j) hb).
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["Policies"] "p'0h02Hah14__x1h21Hh37__arithh44__x2h52H0h62H3h74__ffh88__varmaph95__with:1qh;1rh<2H1h=2H2h>4__x3h?7__sat22h@7__sat23hA7__sat24hB7__sat25hC7__sat26hD7__sat28hE4__x4hF1ahG4__x5hH1chI7__sat27hJ1zhK3HlehL6__sat0hM6__sat1hN2H4hO4Hle0hP2H5hQ1ehR1hhS6__sat2hT2HhhU2_HhV4__p1hW4__x6hX2h'hY2hbhZ1jh[1xi001xh\1yh]3E21h^3HHBh_2Hch`4Hcapha2Hehb3Hejhc5Hhalfhd2Hjhe3Hm1hf3Hm2hg2Hnhh3Hpehi3Hpjhj3_H0hk1bp%0p%1p&0p;1p;2p;3p;4p;5p;6p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710g002`R0p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710g0051R1p4p710p8g006Oj1cTg00g[k103Tg0074j1pTg009fj24Tg00KGj2KTg00Cbj2;j4wTg007Rj21Tg00DJj39Tg00:Bk10:Tg00:bk106Tg00;Bk10PTg00;`k10OTg00<>k10NTg00<ij2lTg00=Lk20JTg00=nk20FTg00>Hk20ETg00?4j3WTg00?Nk30ATg00?mk400Tg00FYj2~Tg00F7k10@Tg00BKj22Tg011Oj28Tg01?]k305Tg01@>k204Tg012kj2GTg013\j2CTg00Bhj1tTg014=j27Tg014]j2DTg015Dj2BTg015kj2FTg016Qj2HTg00I<j3kTg00I_k10KTg00H<j26Tg00J@k50ITg01@`j2XTg01A^j1]Tg00]6j2jTg005Ok101Tg01:Rj13Tg00oGk60DTg01Bcj3hTg00Udj1[Tg00VCj2\Tg00X>j2`Tg00HYj3gTg00mGj1oTg00lGj2}Tg00\8j1nTg01Cfj2{Tg008dj1RTg007oS00j2ATg008JS01j2zTg00U;k20?Tg00Vlj3xTg00@_j4uTg00Anj2ZTP1j8vk60GTg00CAk20>Tg00G`k40=Tg01Dek50<Tg018_k20BTP0k60;Tg01Ekk70CTg00ELj4bTg00Jcj7_Tg00Dnk209Tg00Kcj8aTg00G<k608Tg00jgk40HTg00okk707Tg00WUk30LTg00Xjk30MTf2R0f1R1f0R2'1'2p=Ng00LeR3/K2p=51432p=0P0g00MjR4g00NIR5P5g00NiR6g00LGR7P1g00SPR8P2Cbg00OIR9F_p=M20972p=UP7P1g00MCR:P2Cbp=fP0P4P5P5P6P7P1P:P2CbP9F_p=<f4R:P4P5P5P6f3R;P4P5P5P6P0P9F_P1P2Gap=dAW712p=:P7P1g00T7P2Cbp=rP1P4P5P5P6P2P9F_p=sP1P4P5P5P6P2J08p>02AW723p=?P7P:P;P0P1P2J0Gp=T1201/629W7;p=J14301K12'Ap=E1K011423'Ap=I1412,A0p=Q1612,40p=qP7P0P1P2H0Hp=>1~72p=YP0P4P5P5P6P1P2K07p=iP;P4P5P5P6P0P1P2Gap=^B0L712p=Og00QhR<@0M12p=Vf6R=P4P5P5P6f5R>P:P;P4P5P5P6P0P1P2GaGap==1K31/A2p=e1Z23p=P%32,61p=S1401,A;/A2p=LP:P4P5P5P6P;P0P1P4P5P5P6P2P9F_Gap=y1601/42p=@g00OiR9g00PIS027W2p=mP7P1P8P2Cbp=|g00QCR8#cR?$03R@#cRA#c#pRB/41%p?RC?NC0g01G5S03'4ANCC;,K0PCP:1;C:RD%5CRE%0>11C=RF#5[[RG%0CRHg00S4RIf7RJ=9C1UW0RK11CJRL#0\I^0HRM&0:<RN&06<R<&0P7RO&0O7RP&0N7RQ1l73RR1l7CRS3MS0420JQ6RTP2P0g00RTRU-0F9S0520E20=W9UdB0A731S06H00RUb7b8b9PEP2b3S07bLbMPDPGPKPMPNP<%U1S08PPPQPQ1l7BRM1~78RK'f&0@5RGA<QRKS09DdS0:PTPUb7b8b9X17RD14B2%01S0;[^17S0<P2PJP>O2b3bLbMCw11C:S0=#511C>RV/2C182C/:FXJ71;C>%0=%5L[\Ef8RW=9C1VIX0H11CWRX#0\I^0HPNP<POPP1rSR,sQ-02QPTPUb7b8b9%?CRYg00T^S0>[P2b3bLbM:05VC12CVRZ204CVDT18ZC/:V%p8RZ,1CR[,2F12CLS0?,:2XJ7PC12L2Q0?':XJ71;C=R\%0JS0@%5XS0A[\ER]f9R^=9C1VIX0HR_11C^S0B#0\I^0HR`12CXRa/GCRb%0af:Rc,1CRd,2CRe/8CRf#0\H[RgQ0B,2CS0C/CCRh%tYRiPePCPf17eCCJ[Rf1DeCRjf;Rk,1CS0D,2CRl/7CRm?EmC\ERm1BlCRn1KC3Rof<Rp,1CRq,2CRr/7CRs=ICs[Rs1FrCRtf=Ru,1CS0E,2CRv/8C#?\YRw1HvCRxf>Ry,1CS0F,2CS0G/7CQ0G':\YRzQ0G/8CS0HP7f?R{,1CS0I,2CR|/7CS0JP7PNP<Q08PPAk7KSAk7SKS0K'r,sQPTPUb7b8b9X17122C12C2':^17P2fAS0L,1CR}O1b3b;b:b6b=b<b5b2bLbMbSP[&0KCDT16=Z,1CR[PCP=PZP\P]P_P`PbPgPhPfPjPmPnPsPtPwPxPzQ0HP7Q0JP7PDQ0<P2Q0LP{O2b3b;b:b6b=b<b5b2bLbMbSP\P]P_P`PbPgPhPfPjPmPnPsPtPwPxPzQ0HP7Q0JP7PNP<POPP1l7ZRz9<QRPTPUb7b8b9%0ZP2b3b;b:b6b=b<b5b2bLbMbSI0IDT12CF,:[Q0?/X=S0M%]2XH71XaJ/j2#0^H7e&012S0N%51S0OQ0C7Q1Q0D%3:%32S0P%3rS0Q3qXJ716kZS0R,;CS0S16pZS0T#016uZR[,1C#5[\ES0U16yZRx=9C1VIX0HS0V11Cx#0\I^0HS0W1;CuS0X%0yQ0I#5[\ES0Yf@Rw=9C1VIX0HS0Z11CwRt#0\I^0HS0[1G|CS0\%0|12C}Rs/8CRn#0\H[S0]12CtS0^/CCS0_PsPCPn17sCS0`CJ\iS0a1DsCS0bfBRn,1CRt,2CRm/7CRj?EjC\ES0c1BmCS0dfCS0e,1CS0f,2CRj/7CS0gQ0g5IC\oS0h1FjCS0ifDS0j,1CS0k,2CRf/8C#?\YS0l1HfCS0mfERh,1CS0n,2CRg/7CRb/:g\YS0o18gCS0pP7fFR`,1CS0q,2CR_/7CS0rP7p-0R]PNP<%U0S0s?>1OS0tPPPQPQP4P5P5P6P:J0D%Y?R69k7SS0u9<QKR55iQPGP5C^PTPUb7b8b9X17X47WV12C19Q0212C0S0v,41[^17^47^V]P2%5wfHS0w,1CR]PwPyO4b3b;b:b6b=b<b5b2b?b@bAbBbC9h;l%3;%3lS0x'4%]q%3qS0y#01;C[S0z%0x16{Z,1C#5[\ES0{16wZRx=9C1VIX0HS0|11Cx#0\I^0HS0}1;C{S0~%0wS10%5}[\ES11A9Cn1VIX0HS12%0t\I^0HS131GsCS14%0s18jCS15#0\H[S161CmCS17PjPCQ15Q0gCJ\iS181DjCS1917fCS1:Q1:;EC\ES1;1BfCS1<AICbb\oS1=1FgCS1>18_C#?\YS1?1H_CS1@fGRb,1CS1A,2CRx/7C/:x\YS1B18xCS1CP712C]R[/7CS1DP7g00YJR5#[#[S1E#[S1F#[R4#[,\71\741\75R5'O'Og00YiR4'`/VNP<%U:S1G%U=?>=O7>0%U>R\?>;OS1H7>1PPPQA<QR6S1IPGPQ&038#YR89<QKS1JPGPQ%YARA9MQR%Y@R@9k7S9<QA5iQPGPQ%c?R?#YRA9<QMS1KPGAg768S1L9<QKF=F=PTPUb7b8b9X17X47X>7XE7XG7XW7Q0;141;S1M12C=,4J,eJ14B=S1N16>=S1O,4:[[[[^17^47^>7^E7^G7^W7P2PnfJS1P,1CRSQ1P12CSRD#3S1Q%3SS1R%3nPuPyPwQ0wO:b3b;b:bPbNb6b=b<b?b@bAbBbCb5b218lCP>DTXjIW_WUXH7Q0NQ0OQ0C/XWR~#o7Q11Xe^/}01XlcS1S/j;Q1S#n'4[[[^H7e141W1410S0NQ0SQ0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0_Q0aQ0bQ0cQ0dQ0hQ0iQ0lQ0mQ0oQ0pP7Q0rP7Q1F,\7S1FQ1E,\7S1E/O5'O/`4/VNS0rP<A>\:O?>0O%U;S0p7>1PPPQPQQ04PGPQA<QR8S0oPGAMQRAF=S0mPGPQ%c?#YR?9<QKPGPQPQ1f?6PGPQA<QM8S0lPGA<QK6S0iC^DdF=PTPUb7b8b9X17X47X>7XE7XG7R?%0;S0h%5>[\ES0d141>14=;14B>S0c14:>[[[[^17^47^>7^E7^G7R\P2PwP]Q0wPbP{PcPuPyP`O9b3b;b:b6b=b<b5b2b?b@bAbBbCWKWTXX7XR71{~1Q0NQ1S/{0S0b[[^X7^R7e&011S0a%50S0_PI[140c14:;S0]Q0zQ0{Q0|Q0}Q0~Q11Q12Q13Q14Q16Q17Q18Q19Q1;Q1<Q1=Q1>Q1?Q1@Q1BQ1CP7Q1DP7P?P\P2Q0LPSQ1PfIR\PnPcPuPyQ0wO9b3b;b:b6b=b<b5b2b?b@bAbBbC14>pQ0F%RJR?14?|'eS1CP9P7%PJP3%3Jn0100000020000/S?S1BQ0P%3|R?'63QXJ7g00Pi%?=%02R~11C2Re,:J'AXQ7,z7Q1CQ1BQ0I#3/6?3QP:%?JP7P3142WQ0L,41%R0S1B#5S1CQ1BPjP9P7%P0P3%30n0100000020000Q1B'SS1@Q0f#3%3jS0f3qCL]K]OXH7Q0@Q1016nZ,;CQ0e/6Z#0Q0j/6ZS1?,1C#5[\E16hZS1>=9C1VIX0HQ1>,1C#0\I^0HQ0j,;C%0hQ0q#5[\EA9Cb1VIX0HQ1A#0\I^0H1G_C%0_18[CRJ#0\H[1CxCP[PCPJQ1DCJ\i1D[C11C\S1D,2CS1=/7CRJ?EJC\EQ1=/BC17DCS1<Q1<5IC\o1FDCfK,1CS1;,2CRJ/8C#?\Y1HJCfLS19,1CS18,2CRx/7CS17/:x\Y18xCP7fMS16,1CS14,2CS13/7CP7PNP<Q08PPPQAMQRKS12PGPQ1fzKDyPTPUb7b8b9X17%5214Z1[^17P2fOR?,1CS11Q1PO2b3b;b:b6b=b<b5b2b?b@bAbBbC9hZt%3ZS1P%3tS0~'4%]jQ0f#0%5ZRt?QZfQ1PQ0k#3/Sf5@3Q1?,;CS1?Q1>#016`Z,1C#5[\ES1>16bZRf=9C1VIX0HS0k11Cf#0\I^0HS0f1;C`S0}%0b%5]S0|[\ES0{A9C\1VIX0HS0zQ1D#0\I^0HS0\1G[CS0[%0[18DCR[#0\H[S0ZQ1=/CCS1=PDPCP[Q1<CJ\iS1<1DDCS0Y17JCR[?E[C\ES0X1BJCS0WQ17Q175IC\oS171FxCS0VQ13/8C#?\YS0UQ13/HCS13fNR[9NCCR]/7C/:]\YS0S18]CS1TP7Q11,2CS1U/7CRfP720?7CS1VQ1E5x7/O5/`4/VNP<Q0tPPPQPQQ04PGPQQ1IPGQ12F=PGPQA<QM6PGAMQRzQ0K9<Qz5iQF=PTPUb7b8b9X17X47%00S0tQ0_[\E14B0Q0v9QtZ[[^17^47P2fQRt11CtRzPcP?O4b3b;b:bPbNb6b5b2b?b@bAbBbCQ1?Q1>Q0kQ0fQ0}Q0{Q0zQ0\Q0[Q0ZQ1=Q1<Q0YQ0XQ0WQ17Q0VQ0UQ13Q0SQ1TP7PfP7Q0rP<Q1G?>0OS1TQ1H7>1S1HPPPQPQQ04PGPQA<QRAPGAMQR@F=PGPQQ0oPGPQQ0iPGPQQ1KPGAg7RKQ1L5<QF=F=PTPUb7b8b9X17X47X>7XE7XG7%0:%5=[\EQ0h140;S1LQ1NQ1O9@3:[[[[^17^47^>7^E7^G7P2PzPt12CzS1K#3%3zQ1PPcPuPyP?O9b3b;b:bPbNb6b5b2b?b@bAbBbCCub=b<%R3R=#5P=PmP9P71Z33P3%33n0100000020000%3=Q0~/Sm3@CLeWKWOPWP2P;P0GvW2P2O11:We,A~XQ7,z7Q01P71:^e,A~XQ7%R^R=#5P=PsP9P7%P^P3%3^n0100000020000%3=%3}/Ss3@CLP21:ke,A~Q00Q0;11C1,:p%RuR~#5P~PgP9P7%PuP3%3un0100000020000%3~Q0n#3/Sg3@CLP2Q0hQ0=,:{P7PV142w141\Q1CQ1BPJQ1@Q1;#3%3J3qCL]K]OXH714V{Q0w,4FP9%PLS0wQ02Q001Z12#m1:01#tRF[1:12#t1Z01#m[RV1Z;0#m\F20>12P2n2001000000120000000X\7X[7PV^\7^[7P2PXP31;CWS00%0^%5d[\ES1@1;C^S1B%0cQ0D#5[\ES1CA9Cp1VIX0HS0=%0q\I^0HS0n16[ZS0;,;CS0116?ZS0@#0fPS10/6ZS0~,1CS1P#5[\ES0S16tZR[=9C1VIX0HS1311C[#0\I^0HS0UQ10,;CS0V%0tfRRt,1CS17#5[\ES0WfSRq=9C1VIX0HS0X11CqRV#0\I^0HS0YQ17,2CS1</GCS1=Q1<#0fTS0Z,1CS0[,2CRF/8CRJ#0\H[S0\12CVRV/CCS0zPFPCPJ17FCS0{CJ\iS0}1DFCS0ffUS0k,1CS1>,2CRJ/7CR\?E\C\ES1?1BJCS0vfVS1E,1CS1W,2CRg/7CS1XQ1X5IC\oS1Y1FgCS1ZfW9NCCR~/8CS1[#?\YS1\1H~CS1]fXS1^9NCCRe/7CR}/:e\YS1_18eCS1`P7fY9NCCR=/7CRfP7PyP2Q0jO2XFES1aQ0|^FES0|PwP2PhO2XFEQ1D#5^FEPNP<Q08PPPQPQQ04PGQ12C^S12PG1rKR,sQ-02QC^PTPUb7b8b9X17Q0O\E%?1Q0>[[^17P2PSP1O2b3b2bDb;b:bNb6b=b<b5b?b@bAbBbCbIbDb2O3b2H0=Q02Q0w5W9P9Q02P9P7P2PZQ0Cn0100000020000S0C#5Q0CPxP9P7P2P3Q0B#3n0100000020000Q0C#3Q18#3S0C%3xS02'63@CLXk9PCPWQ00Q1@A9Ck1VIX0HQ0D#0\I^0HQ16/6Z,;CQ0;#0Q0@,1C#5[\EQ0~=9C1VIX0HQ1P#0\I^0H1;C?Q10#0%5z[\EA9Ct1VIX0HQ17#0\I^0HQ1K/GCQ1K#018VCRz#0\H[Q1</CCPVPCPz17VCCJ\i1DVCQ0{Q0{;EC\E1BFCAIC\\\o1FJC18gCR\#?\Y1HgC17~CRV/:~\YQ1[P7P}P7PyP2Q0eO2XFEQ1A#5^FEQ07bDb;b:b6b=b<b5b2b?b@bAbBbCbIbDP:CwQ0AP^Q19P>Q1BQ1CQ0=Q0nQ01Q0SQ13Q0UQ0VQ0WQ0XQ0YQ1=Q0\Q0zQ0}Q0fQ1?Q0vQ1YQ1ZQ1\Q1]Q1_Q1`P7PfP7Q1aQ0|PNP<Q08PPQ0:PTP2P0Q05Q06H00b7b8b9X17Q0<P2f\R0fZRzO2b3bDb;b:b6b=b<b5b2b?b@bAbBbCbIbDPx1Kd2XJ7Q1BQ1CQ0=Q0nQ01Q0SQ13Q0UQ0VQ0WQ0XQ0YQ1=Q0\Q0zQ0}Q0fQ1?Q0vQ1YQ1ZQ1\Q1]Q1_Q1`P7PfP7Q1aQ0|Q0rP<Q0sQ1G?>;O7>1PPPQPQQ04PGPQQ0oPGAMQR6F=S0oPGPQA<QK@PGPQPQQ0u,|@PGPQQ0lPGPQQ0u,|KDyDdF=PTPUb7b8b9X17X47X>7XE7Q0h%5;[\ERO141:12C;Rx,K>Q0c12C>S04,K:[[[[^17^47^>7^E7P2f[R?P011C0S1GQ1DPkPnQ1^PzO8b3bDb;b:b6b=b<b5b2b?b@bAbBbCbIbDQ19/6Z,1CPhDTI0<Q0BQ18'4Q14=hd2%3dQ14#3'41;CkS14%0pQ0E#5[\ES0EA9Cy1VIX0HS0BQ0F#0\I^0HS19Q0~,;C%0[16tZRd,1C#5[\E16qZRh=9C1VIX0H11ChRh#0\I^0H1;Ct%0qQ0[#5[\EQ0k=9C1VIX0HQ1>#0\I^0H1GFC%0F%0\\H[1CJCPgPCP\Q1XCJ\i1DgCAEVVC\E1B~CAIC}}\o1FeC18=C#?\Y1H=CANCCzRz/7C/:z\Y18zCR\P7ANCC?R?/7CRFP7PyP2P`O2XFE%5S^FEQ1F,O5/`4-0B5RS/VNP<Q0sQ0p7>1S0sPPPQQ0oPGPQQ0iPGPQQ0lPGQ0KQ0u5<QRtC^F=PTPUb7b8b9X17X47X>7Q0N14B:12C:RB,4x[[\O^17^47^>7P2f^Rx11CxQ1;PkQ0LP0O6b3bDb;b:b6b=b<b5b2b?b@bAbBbCbIbD9hl]Q0x%3]'4Q1U,4r,erQ0yQ0QQ11#3Q1U'S3@1;CpS0y%0uQ0F#5[\ES0FA9C{1VIX0HS0QQ0I#0\I^0HS0I1;C[S1U%0d%5h[\ERhQ0Z/6ZRd=9C1VIX0HR[11Cd#0\I^0HRd1;CqRqQ0Z#0Q1>#5[\ER{Q1E=9C1VIX0HRrQ1W#0\I^0HR]1GJCRl%0JQ1[#0\H[RJ1CgCRgP~PCQ1[PVCJ\iRV1D~CR~AE}}C\ER}1BeCReAICff\oRf1F=CR=%?\\YR\1HzCRz1:F?\YRF18?CR?P7Q1G,2C/7CR0P7PyP2PbO2XFERbQ1;#5^FERxQ1VQ1F5x7/O5/`4/VN,VSP<Q0sPPPQQ0oPGPQQ12PGPQQ0iPGPQQ0lPGQ0K9MQR=iQtF=F=PTPUb7b8b9X17X47X>7Q0_\EQ1LQ0cQ04,4B,eB[[[\O^17^47^>7P2f_RO11CORBQ18PkP1Pnf]RnO7b3bDb;b:b6b=b<b5b2b?b@bAbBbCbIbDQ0yQ0FQ0QQ0IQ1UPhP[PdPqP{PrP]PlPJPgPVP~P}PePfP=P\PzPFP?P7P0P7PbPxQ0rP<Q1HPPPQPQ1f6APGPQQ1JPGPQA<QM@PGAg7K6R6Ag78A5<QF=DdPTPUb7b8b9X17X47X>7XE7XG7Q1MQ1MQ1NQ1O9@;:[[[^17^47^>7^E7^G7P2PO12CB#3%3BQ02Q0CPwQ0LPnO8b3bDb;b:b6b=b<b5b2b?b@bAbBbCbIbDCubfbebbbh%PXP2J0;b2%RLRX#5PXPDP9P7Q0wP3%3LRDn0100000020000%3XQ1RQ1Q'63@CLeWKWOPwP2PkPcGvW2WaP1P2O2n2001000000121000000W2XQ7P1P2O2n2001000000121100000W2P2O1n200100000021100011000Q0HPWDTbKWOWTWUW`XR7XH7Q0aQ0_Q1S/};[Q0bQ0]%R>R;#5P;1XvpRp#oP9P7%P>P31jp>n01000000200001jp;%np3@CL[[[[^R7^H7eP:Q0M#oQ03'4ePLQ0P%3aRp'6#0XJ7%]L%0D%]a%0p16^Z,;C16cZ#0Q0R,1C#5[\EQ0T=9C1VIX0HQ0T,1C#0\I^0HQ14Q0EQ0BQ191GvC%0v18|CRv#0\H[Q0G/CCP|PCPvQ0JCJ\i1D|CQ0^/7CR|?E|C\EQ0^/BCQ0`Q0`5IC\o1FsC18mC#?\Y1HmCQ0g/:j\YQ15P7Q1:P7Q0rP<Q1TQ0p7>1PPPQQ0mPGPQQ1IPGPQQ09PGPQQ0lPGA<QR6F=F=PTPUb7b8b9X17X47X>7XE7Q0dQ0tQ0tQ0c16:>#0[[[[^17^47^>7^E7P2Q0qP`%3_Q0q#3PcPuPyQ0jO8b3b;b:bPbNb6b=b<b?b@bAbBbCb5b2Q0?/8CP1DTQ0M#n#0eK0Cb]bcbiW^WgWdXY7XZ7P1P2O2XY7XZ7o"). Qed.

(* [comment removed for export] *)
Definition SMZ : Z := 2 ^ 29 - 8.
Definition ZMAX : Z := 2 ^ 29.
Definition PME : sink_policy := SP_T ZMAX SMZ.
Lemma PME_ok : sink_policy_ok PME.
Proof.
ltac2:(KReplay.run1 (kr_t_NemSink ()) ["Policies"] "h02Hah17__arithh24__ffh38__varmaph45__with56__sat0h66__sat1h76__sat2h86__sat3h96__sat4h:6__sat5p;1p;2p;4p;3p;5p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710p10051p4p710p8g00g[j14Tg006Oj10Tg0074j13Tg00:Bj1CTg00:bj1OTg00;Bj1JTg00;`j1GTg00<>j1FTg00<ij27Tg00ELj4<Tg00=Lj2ATg00=nj2@Tg00>Hj2NTg00?4j3MTg00?Nj3LTg00?mj4ITg009fj29Tg00Cbj25Tg00KGj22Tg007Rj2:Tg00DJj38Tg00ZUj16Tg019Kj3;Tg00I<j3ETg00jDj3>Tg00BKj2HTg00^6j2?Tg01Gkj5DTg00aYj1KTg00Jcj7BTf1R0g00Mjg00NIR1P1g00NiR1f0R2g00OIFBp==g00LeR3/92p=1g00QCR4#4#4R5#0R6#0R7#3R8g01HlR9g00QhR:#CR;%O:R:g00LGR<#JR=%G<R>%F<R?P<%04R4#4#0#0#3R@,7<g00MCRA17<8C<'=1A?1R1P2f2RBg00OiRCg00RTRD'@1N2B=MCDdAL<30CIRDb2b3b419@8P2b1%34R@/58RC123@RB%181:@8RE,23[[RF%1@RGg00S4RHA8@80UW0R8%1E\H^0GRI%04#0R4#0RJ#3RK,5@%1K1:@KRL,23[\BA8@K0VHX0G%1L\H^0G%45#0R5#3RK,5@%1K1:@KRM,23[\BA8@K0VHX0G%1M\H^0GP;P:P=P>P<17<@RK%679;<K5E<R7PA%659;<K%6J9;<K5><C<,=?P1PDb2b3b41H@ERE1?ML'9RMP2b1b5b6b7b8b9b:PMeg01G5,9Ee%46R6#3RM,5@%1M1:@MRL,23[\BA8@M0VHX0G%1L\H^0GPCPFP8PIP;P:P=P>P<%669;<K%34R4,7<5><g00SPP7C<,=?P1PDb2b3b41?L4/2ER4P2b1b5b6b7b8P4e129EeDDg01Ii#Keo"). Qed.
End Policies.

End NESK.

End NemSink.
Module PnV8.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmTxtSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQV8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive v8 : Type := V8Null | V8Blk (b n c : Z).
Definition v8_size (x : v8) : Z := match x with V8Null => 0 | V8Blk _ n _ => n end.
Definition v8_cap (x : v8) : Z := match x with V8Null => 0 | V8Blk _ _ c => c end.
Definition v8_data (x : v8) : Z := match x with V8Null => 0 | V8Blk b _ _ => b end.
Definition v8_own (x : v8) : list (Z * Z) := match x with V8Null => [] | V8Blk b _ c => [(b, c)] end.
(* [comment removed for export] *)
Definition v8_clear (x : v8) : v8 := match x with V8Null => V8Null | V8Blk b _ c => V8Blk b 0 c end.
(* [comment removed for export] *)
Abbreviation REQB := (2 ^ 26 + 2 ^ 14).
Abbreviation CAPB := (2 ^ 27 + 2 ^ 15).
Abbreviation POTB := (2 ^ 28 + 2 ^ 16).

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
(* [comment removed for export] *)
Definition v8_at (M : word -> option byte) (v : Z) (x : v8) : Prop :=
  L5.defined M v 24 /\ acc M v 24 /\
  match x with
  | V8Null => L5.u64_at segs M v 0 /\ L5.u64_at segs M (v + 8) 0 /\ L5.u64_at segs M (v + 16) 0
  | V8Blk b n c => L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + n) /\ L5.u64_at segs M (v + 16) (b + c)
                   /\ 0 <= n <= c /\ 1 <= c <= CAPB /\ 4096 <= b /\ b mod 16 = 0
                   /\ L5.defined M b c /\ acc M b n /\ ann M b n c
  end.
End Model.

(* [comment removed for export] *)
Definition v8_ok (x : v8) (g : Z) : Prop :=
  match x with V8Null => g = 0 | V8Blk _ _ c => 1 <= g <= 28 /\ 2 ^ (g - 1) <= c end.
(* [comment removed for export] *)
Definition pot_v8 (L : heap_layout) (x : v8) (g : Z) : credit :=
  (hl_k_per_malloc L * (28 - g), (POTB - 2 * v8_cap x) + (28 - g) * hl_b_overhead L).
(* [comment removed for export] *)
Definition v8_grow_ok (x : v8) (n : Z) : Prop := n <= v8_cap x \/ n <= REQB.

Lemma v8_ok_cap x g : v8_ok x g -> 0 <= g <= 28 /\ (g = 0 <-> x = V8Null).
Proof. destruct x as [|b n c]; cbn; [intros ->; split; [lia| tauto]| intros [H1 H2]; split; [lia| split; [lia| discriminate]]]. Qed.
(* [comment removed for export] *)
Lemma v8_ok_blk x g b n c : v8_ok x g -> x = V8Blk b n c -> 1 <= g <= 28 /\ 2 ^ (g - 1) <= c.
Proof. intros OK ->. cbn in OK. exact OK. Qed.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation iss_at := (PM.iss_at segs A PMSP.T3).
Abbreviation nullis_at := (PM.nullis_at segs A PMSP.T3).
Abbreviation src_fields_at := (PM.src_fields_at segs PMSP.T3).
Abbreviation v8_atP := (v8_at segs PMSP.T3 PMSP.T4).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vu8_grow_spec (pc : Z) (is_append : bool) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (v a sp r g : Z) (x : v8),
    hi_heap HI (v8_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 a -> sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 ->
    v8_atP M v x -> v8_ok x g ->
    (* [comment removed for export] *)
    (if is_append then 1 <= a /\ v8_size x + a < 2 ^ 64 else 0 <= a < 2 ^ 64) ->
    v8_grow_ok x (if is_append then v8_size x + a else a) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : v8) (g' : Z) (cr' : credit),
        regs_preserved R R' -> v8_atP M' v x' -> v8_size x' = (if is_append then v8_size x + a else a) -> v8_ok x' g' ->
        v8_cap x <= v8_cap x' ->
        (v8_size x' <= v8_cap x -> v8_own x' = v8_own x /\ v8_cap x' = v8_cap x /\ g' = g) ->
        L5C.hpres L LB sp (pm_scr 1) [(v, 24)] M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (v8_own x' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
Definition vu8_resize_spec (pc : Z) : Prop := vu8_grow_spec pc false.
Definition vu8_append_spec (pc : Z) : Prop := vu8_grow_spec pc true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record vowner : Type := VOWN {
  vw_at  : (word -> option byte) -> PM.srcst -> v8 -> Z -> list (Z * Z) -> Prop;
  vw_os  : Z; vw_ois : Z; vw_ov : Z; vw_lo : Z; vw_hi : Z
}.
Record vowner_ok (V : vowner) : Prop := {
  vo_src : forall M src x g OB, vw_at V M src x g OB ->
             src_fields_at M (vw_os V) (vw_ois V) (vw_ois V + 16) src /\ nullis_at M (vw_os V + 8) /\ L5.defined M (vw_os V) 296
             /\ v8_atP M (vw_ov V) x /\ v8_ok x g;
  vo_lay : vw_lo V <= vw_os V /\ vw_os V + 296 <= vw_hi V /\ vw_lo V <= vw_ois V /\ vw_ois V + 272 <= vw_hi V
           /\ vw_lo V <= vw_ov V /\ vw_ov V + 24 <= vw_hi V /\ vw_hi V <= hl_sptop L /\ vw_hi V <= 2 ^ 47
           /\ vw_os V mod 8 = 0 /\ vw_ois V mod 8 = 0 /\ vw_ov V mod 8 = 0 /\ 4096 <= vw_lo V
           /\ (vw_os V + 296 <= vw_ois V \/ vw_ois V + 272 <= vw_os V)
           /\ (vw_ov V + 24 <= vw_os V \/ vw_os V + 296 <= vw_ov V) /\ (vw_ov V + 24 <= vw_ois V \/ vw_ois V + 272 <= vw_ov V)
           /\ hl_ceil L <= vw_lo V /\ hl_errno L + 4 <= vw_lo V;    (* [comment removed for export] *)
  (* [comment removed for export] *)
  vo_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst)
             (x x' : v8) (g g' : Z) (OB : list (Z * Z)) (cr : credit) (VM : VmMaps),
             sp <= vw_lo V -> vw_at V M src x g OB ->
             hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= vw_lo V \/ vw_hi V <= fst b) (PM.src_own src ++ v8_own x ++ OB) ->
             (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                                   /\ (forall B' m', In (B', m') (v8_own x) -> fst b + snd b <= B' \/ B' + m' <= fst b)) ->
             (* [comment removed for export] *)
             Forall (fun r => (fst r + snd r <= vw_lo V \/ vw_hi V <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)) Wx ->
             L5C.hpres L (OB ++ LBX) sp scr (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)] ++ Wx) M M' ->
             src_fields_at M' (vw_os V) (vw_ois V) (vw_ois V + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             v8_atP M' (vw_ov V) x' -> v8_ok x' g' ->
             vw_at V M' src' x' g' OB
}.
(* [comment removed for export] *)
Definition src_of_vw (V : vowner) (x : v8) (g : Z) : PGS.owner :=
  {| PGS.ow_at := fun M src OB' => exists OB, OB' = v8_own x ++ OB /\ vw_at V M src x g OB;
     PGS.ow_os := vw_os V; PGS.ow_ois := vw_ois V; PGS.ow_lo := vw_lo V; PGS.ow_hi := vw_hi V;
     PGS.ow_win := fun M src OB' p k => exists b n c, x = V8Blk b n c /\ b <= p /\ p + k <= b + c /\ 0 <= k |}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_span_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 6 ->
    sp <= vw_lo V ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (vw_ov V) -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        PMSP.consumed src src' sm sm' = n ->
        ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ v8_own x' ++ OB) ptr n) ->
        L5.defined M' ptr n ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 6) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition srd_read_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 5 ->
    sp <= vw_lo V ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 (vw_ov V) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> v8_size x = 0 ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed src src' sm sm' = d -> v8_size x' = d ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 5) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pot_v8_grow L x g c' :
  0 <= hl_k_per_malloc L -> v8_ok x g -> 2 * v8_cap x <= c' ->
  forall b' n', v8_ok (V8Blk b' n' c') (g + 1) ->
  fst (pot_v8 L x g) - hl_k_per_malloc L = fst (pot_v8 L (V8Blk b' n' c') (g + 1))
  /\ snd (pot_v8 L x g) - (c' + hl_b_overhead L) >= snd (pot_v8 L (V8Blk b' n' c') (g + 1)).
Proof. intros K OK Hc b' n' OK'. unfold pot_v8. cbn [fst snd v8_cap]. split; lia. Qed.

(* [comment removed for export] *)
Lemma v8_ok_grow x g b' n' c' :
  v8_ok x g -> 2 * v8_cap x <= c' -> 1 <= c' <= CAPB -> v8_ok (V8Blk b' n' c') (g + 1).
Proof.
  intros OK H2 Hc. destruct x as [|b n c]; cbn in *.
  - subst g. cbn. split; [lia|]. change (2 ^ 0) with 1. lia.
  - destruct OK as [Hg Hp]. cbn. replace (g + 1 - 1) with ((g - 1) + 1) by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    split; [|lia].
    destruct (Z_le_gt_dec (g + 1) 28) as [H|H]; [lia|exfalso].
    assert (X : 2 ^ 27 <= 2 ^ (g - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

End PQV8.

End PnV8.
Module PnQModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAX_DEPTH : Z := 1024.        (* [comment removed for export] *)
Definition PSZ : Z := 24.                (* [comment removed for export] *)
Definition LSZ : Z := 24.                (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OFF_SRC : Z := 24.
Definition OFF_MAXD : Z := 320.
Definition OFF_TB : Z := 328.
Definition OFF_BB : Z := 352.
Definition OFF_STK : Z := 376.
Definition PSIZE : Z := 400.
(* [comment removed for export] *)
Definition AOFF_DV : Z := 8.             (* [comment removed for export] *)
Definition AOFF_DEST : Z := 16.          (* [comment removed for export] *)
Definition AOFF_KEY : Z := 24.           (* [comment removed for export] *)
Definition AOFF_KB : Z := 48.            (* [comment removed for export] *)
Definition AOFF_LV : Z := 72.            (* [comment removed for export] *)
Definition ASIZE : Z := 96.
(* [comment removed for export] *)
Definition SMB : Z := 7 * 2 ^ 26 + 2.
Definition SMK : Z := 2 ^ 27 + 64.
Definition KCAP : Z := 2 ^ 31.           (* [comment removed for export] *)
Definition GMAX : Z := 28.               (* [comment removed for export] *)

(* [comment removed for export] *)
Record mstate : Type := MS { ms_mode : Z; ms_len : Z; ms_idx : Z }.
Definition ms_root : mstate := MS 0 0 0.
Definition mode_bottom (m : Z) : Prop := m = 0 \/ m = 1.
Definition mode_cont (m : Z) : Prop := m = 2 \/ m = 3 \/ m = 4.
Definition mstate_ok (s : mstate) : Prop :=
  0 <= ms_mode s <= 4 /\ 0 <= ms_len s < 2 ^ 64 /\ 0 <= ms_idx s <= ms_len s.

(* [comment removed for export] *)
Record alvl : Type := AL { lv_t : Z; lv_k : Z; lv_eo : Z }.
Definition lv_root : alvl := AL 0 0 1.
Definition alvl_ok (x : alvl) : Prop :=
  (lv_t x = 0 \/ lv_t x = 1) /\ 0 <= lv_k x <= 2 /\ (lv_eo x = 0 \/ lv_eo x = 1) /\ (lv_k x <> 2 -> lv_eo x = 1).

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable vp_parser : Z.      (* [comment removed for export] *)
Variable vp_adaptor : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mstate_at (M : word -> option byte) (a : Z) (s : mstate) : Prop :=
  L5.u32_at segs M a (ms_mode s) /\ L5.u64_at segs M (a + 8) (ms_len s) /\ L5.u64_at segs M (a + 16) (ms_idx s).
Definition mvec_at (M : word -> option byte) (v b k : Z) (stk : list mstate) : Prop :=
  L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + PSZ * Z.of_nat (length stk)) /\ L5.u64_at segs M (v + 16) (b + PSZ * 2 ^ k)
  /\ 0 <= k <= 11 /\ Z.of_nat (length stk) <= 2 ^ k /\ b mod 16 = 0
  /\ L5.defined M b (PSZ * 2 ^ k) /\ acc M b (PSZ * Z.of_nat (length stk)) /\ ann M b (PSZ * Z.of_nat (length stk)) (PSZ * 2 ^ k)
  /\ (forall i, (i < length stk)%nat -> mstate_at M (b + PSZ * Z.of_nat i) (nth i stk ms_root)).
Definition mvec_own (b k : Z) : list (Z * Z) := [(b, PSZ * 2 ^ k)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Record mpst : Type := MPST {
  p_more : Z; p_done : Z; p_depth : Z;
  p_src : PM.srcst;
  p_tb : PM.vstr; p_tg : Z;            (* [comment removed for export] *)
  p_bb : PQV8.v8; p_bg : Z;            (* [comment removed for export] *)
  p_sb : Z; p_sk : Z; p_stk : list mstate   (* [comment removed for export] *)
}.
Definition mparser_at (M : word -> option byte) (op ois : Z) (s : mpst) : Prop :=
  L5.u64_at segs M op vp_parser /\ L5.defined M op PSIZE /\ acc M op 24
  /\ L5.u8_at segs M (op + 8) (p_more s) /\ L5.u8_at segs M (op + 9) (p_done s) /\ L5.u32_at segs M (op + 12) (p_depth s)
  /\ L5.u8_at segs M (op + 16) 0 /\ L5.u32_at segs M (op + 20) 0
  /\ PM.nullis_at segs A acc M (op + OFF_SRC + 8)
  /\ PM.src_fields_at segs acc M (op + OFF_SRC) ois (ois + 16) (p_src s)
  /\ L5.u32_at segs M (op + OFF_MAXD) MAX_DEPTH /\ acc M (op + OFF_MAXD) 8
  /\ PM.vstr_at segs acc M (op + OFF_TB) (p_tb s)
  /\ PQV8.v8_at segs acc ann M (op + OFF_BB) (p_bb s)
  /\ mvec_at M (op + OFF_STK) (p_sb s) (p_sk s) (p_stk s)
  /\ (p_more s = 0 \/ p_more s = 1) /\ (p_done s = 0 \/ p_done s = 1) /\ 0 <= p_depth s <= MAX_DEPTH + 1.
(* [comment removed for export] *)
Definition mrest_own (s : mpst) : list (Z * Z) := mvec_own (p_sb s) (p_sk s) ++ PQV8.v8_own (p_bb s) ++ PM.vs_own (p_tb s).
Definition mparser_own (s : mpst) : list (Z * Z) := PM.src_own (p_src s) ++ mrest_own s.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tb_okM (x : PM.vstr) : Prop := match x with PM.VShort n => 0 <= n <= 22 | PM.VLong c _ _ => 26 <= c end.
Definition mgrow_ok (s : mpst) : Prop := tb_okM (p_tb s) /\ PQV8.v8_ok (p_bb s) (p_bg s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kstr_at (M : word -> option byte) (o : Z) (s : PM.vstr) : Prop :=
  L5.defined M o 24 /\ acc M o 24 /\
  match s with
  | PM.VShort n => 0 <= n <= 22 /\ L5.u8_at segs M o (2 * n)
  | PM.VLong c n p => L5.u64_at segs M o (c + 1) /\ L5.u64_at segs M (o + 8) n /\ L5.u64_at segs M (o + 16) p
                      /\ 0 <= n < c /\ 26 <= c <= KCAP /\ c mod 2 = 0 /\ L5.defined M p c /\ acc M p c
  end.
Definition ks_alloc (s : PM.vstr) : Z := match s with PM.VShort _ => 0 | PM.VLong c _ _ => c end.
Definition ks_ok (SM : Z) (s : PM.vstr) (g : Z) : Prop :=
  0 <= PM.vs_size s <= SM /\ SM <= 2 ^ 29 /\
  match s with
  | PM.VShort _ => g = 0
  | PM.VLong c _ _ => 1 <= g <= GMAX /\ 48 * 2 ^ (g - 1) <= c /\ c mod 8 = 0 /\ c <= 2 * SM + 48
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition alvl_at (M : word -> option byte) (a : Z) (x : alvl) : Prop :=
  L5.u32_at segs M a (lv_t x) /\ L5.u32_at segs M (a + 4) (lv_k x) /\ L5.u32_at segs M (a + 8) (lv_eo x) /\ L5.defined M a LSZ.
Definition lvec_at (M : word -> option byte) (v b k : Z) (lv : list alvl) : Prop :=
  L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + LSZ * Z.of_nat (length lv)) /\ L5.u64_at segs M (v + 16) (b + LSZ * 2 ^ k)
  /\ 0 <= k <= 11 /\ Z.of_nat (length lv) <= 2 ^ k /\ b mod 16 = 0
  /\ L5.defined M b (LSZ * 2 ^ k) /\ acc M b (LSZ * Z.of_nat (length lv)) /\ ann M b (LSZ * Z.of_nat (length lv)) (LSZ * 2 ^ k)
  /\ (forall i, (i < length lv)%nat -> alvl_at M (b + LSZ * Z.of_nat i) (nth i lv lv_root)).
Definition lvec_own (b k : Z) : list (Z * Z) := [(b, LSZ * 2 ^ k)].

Record ast : Type := AST {
  a_lv : list alvl; a_lb : Z; a_lk : Z;    (* [comment removed for export] *)
  a_key : PM.vstr; a_kg : Z;               (* [comment removed for export] *)
  a_kb : PM.vstr; a_kbg : Z                (* [comment removed for export] *)
}.
Definition adaptor_at (M : word -> option byte) (oa ov : Z) (st : ast) : Prop :=
  L5.u64_at segs M oa vp_adaptor /\ L5.u64_at segs M (oa + AOFF_DV) (pa_vp_visitor A) /\ L5.u64_at segs M (oa + AOFF_DEST) ov
  /\ L5.defined M oa ASIZE /\ acc M oa 24
  /\ kstr_at M (oa + AOFF_KEY) (a_key st) /\ kstr_at M (oa + AOFF_KB) (a_kb st)
  /\ lvec_at M (oa + AOFF_LV) (a_lb st) (a_lk st) (a_lv st).
Definition aown (st : ast) : list (Z * Z) := lvec_own (a_lb st) (a_lk st) ++ PM.vs_own (a_key st) ++ PM.vs_own (a_kb st).
(* [comment removed for export] *)
Definition adaptor_W (oa : Z) : list L5.range := [(oa + AOFF_KEY, 72)].

End Model.

(* [comment removed for export] *)
Definition lv_shape (lv : list alvl) : Prop :=
  (1 <= length lv)%nat /\ Z.of_nat (length lv) <= MAX_DEPTH + 1
  /\ nth 0 lv lv_root = lv_root
  /\ (forall i, (1 <= i < length lv)%nat -> lv_k (nth i lv lv_root) <> 0)
  /\ (forall i, (i < length lv)%nat -> alvl_ok (nth i lv lv_root)).
Definition adaptor_ok (st : ast) : Prop :=
  lv_shape (a_lv st) /\ ks_ok SMK (a_key st) (a_kg st) /\ ks_ok SMB (a_kb st) (a_kbg st).
Definition nlv (st : ast) : Z := Z.of_nat (length (a_lv st)).
Definition kbsize (st : ast) : Z := PM.vs_size (a_kb st).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cpl (s : mpst) (st : ast) : Prop := length (a_lv st) = length (p_stk s).
Definition acct (n : Z) (s : mpst) (st : ast) (sm : PM.strm) : Prop :=
  kbsize st + 2 * nlv st + 7 * PM.unread (p_src s) sm <= 7 * n + 2 /\ 0 <= n < 2 ^ 26.
(* [comment removed for export] *)
Definition acct_d (d n : Z) (s : mpst) (st : ast) (sm : PM.strm) : Prop :=
  kbsize st + 2 * nlv st + 7 * PM.unread (p_src s) sm + d <= 7 * n + 2 /\ 0 <= n < 2 ^ 26.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition with_src (s : mpst) (src' : PM.srcst) : mpst :=
  MPST (p_more s) (p_done s) (p_depth s) src' (p_tb s) (p_tg s) (p_bb s) (p_bg s) (p_sb s) (p_sk s) (p_stk s).
Definition with_src_bb (s : mpst) (src' : PM.srcst) (bb' : PQV8.v8) (bg' : Z) : mpst :=
  MPST (p_more s) (p_done s) (p_depth s) src' (p_tb s) (p_tg s) bb' bg' (p_sb s) (p_sk s) (p_stk s).
Definition vec_rest_own (s : mpst) : list (Z * Z) := mvec_own (p_sb s) (p_sk s) ++ PM.vs_own (p_tb s).
Section Owners.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable vp_parser : Z.
(* [comment removed for export] *)
Definition src_owner (op ois lo hi : Z) (s : mpst) : PGS.owner :=
  {| PGS.ow_at := fun M src OB => mparser_at segs A acc ann vp_parser M op ois (with_src s src) /\ OB = mrest_own s;
     PGS.ow_os := op + OFF_SRC; PGS.ow_ois := ois; PGS.ow_lo := lo; PGS.ow_hi := hi;
     PGS.ow_win := fun M src OB p k => False |}.
Definition vec_owner (op ois lo hi : Z) (s : mpst) : PQV8.vowner :=
  {| PQV8.vw_at := fun M src x g OB => mparser_at segs A acc ann vp_parser M op ois (with_src_bb s src x g) /\ PQV8.v8_ok x g
                                        /\ OB = vec_rest_own s;
     PQV8.vw_os := op + OFF_SRC; PQV8.vw_ois := ois; PQV8.vw_ov := op + OFF_BB; PQV8.vw_lo := lo; PQV8.vw_hi := hi |}.
End Owners.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pot_vstack (L : heap_layout) (k : Z) : credit :=
  (hl_k_per_malloc L * (11 - k), 24 * (2 ^ 12 - 2 ^ (k + 1)) + (11 - k) * hl_b_overhead L).
Definition pot_ks (L : heap_layout) (SM : Z) (s : PM.vstr) (g : Z) : credit :=
  (hl_k_per_malloc L * (GMAX - g), (4 * SM + 128 - 2 * ks_alloc s) + (GMAX - g) * hl_b_overhead L).
(* [comment removed for export] *)
Definition pot_textM (L : heap_layout) (x : PM.vstr) : credit :=
  match x with
  | PM.VShort _ => (2 * hl_k_per_malloc L, 74 + 2 * hl_b_overhead L)
  | PM.VLong c _ _ => if c <? 45 then (hl_k_per_malloc L, 48 + hl_b_overhead L) else (0, 0)
  end.
Definition pot_mparser (L : heap_layout) (s : mpst) : credit :=
  PM.credit_add (pot_vstack L (p_sk s))
    (PM.credit_add (pot_textM L (p_tb s)) (PQV8.pot_v8 L (p_bb s) (p_bg s))).
Definition pot_adaptor (L : heap_layout) (st : ast) : credit :=
  PM.credit_add (pot_vstack L (a_lk st))
    (PM.credit_add (pot_ks L SMK (a_key st) (a_kg st)) (pot_ks L SMB (a_kb st) (a_kbg st))).
Definition pot_run (L : heap_layout) (s : mpst) (st : ast) : credit := PM.credit_add (pot_mparser L s) (pot_adaptor L st).
(* [comment removed for export] *)
Definition TSRES : credit := (40, 5 * 2 ^ 20).

End PQM.

End PnQModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef.
Module NemModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module NEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAX_DEPTH : Z := PQM.MAX_DEPTH.   (* [comment removed for export] *)
Definition ESZ : Z := 24.                    (* [comment removed for export] *)
Definition ESIZE : Z := 56.                  (* [comment removed for export] *)
Definition EKMAX : Z := 12.                  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition TAG_NONE : Z := 0.
Definition TAG_ESEC : Z := 5.
Definition TAG_ENANO : Z := 7.
(* [comment removed for export] *)
Definition EC_TOO_MANY : Z := 6.
Definition EC_TOO_FEW : Z := 7.
Definition EC_DEPTH : Z := 8.
Definition EC_BADTS : Z := 10.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hdr_str (n : Z) : Z := if n <=? 31 then 1 else if n <=? 255 then 2 else if n <=? 65535 then 3 else 5.
Definition hdr_bin (n : Z) : Z := if n <=? 255 then 2 else if n <=? 65535 then 3 else 5.
Definition hdr_ext (n : Z) : Z :=
  if (n =? 1) || (n =? 2) || (n =? 4) || (n =? 8) || (n =? 16) then 2 else if n <=? 255 then 3 else if n <=? 65535 then 4 else 6.
Definition hdr_cont (n : Z) : Z := if n <=? 15 then 1 else if n <=? 65535 then 3 else 5.
Definition w_u64 (v : Z) : Z := if v <=? 127 then 1 else if v <=? 255 then 2 else if v <=? 65535 then 3 else if v <=? 4294967295 then 5 else 9.
Definition w_i64 (v : Z) : Z :=
  if 0 <=? v then w_u64 v else if -32 <=? v then 1 else if -128 <=? v then 2 else if -32768 <=? v then 3 else if -2147483648 <=? v then 5 else 9.
Definition w_ts (s : Z) : Z := if s <? 2 ^ 32 then 6 else if s <? 2 ^ 34 then 10 else 15.
(* [comment removed for export] *)
Definition w_double_ok (w : Z) : Prop := w = 5 \/ w = 9.
Definition w_tstext_ok (w : Z) : Prop := w = 0 \/ w = 6 \/ w = 10 \/ w = 15.

Lemma hdr_str_le n : 1 <= hdr_str n <= 5.  Proof. unfold hdr_str. destruct (n <=? 31); [lia|]. destruct (n <=? 255); [lia|]. destruct (n <=? 65535); lia. Qed.
Lemma hdr_bin_le n : 2 <= hdr_bin n <= 5.  Proof. unfold hdr_bin. destruct (n <=? 255); [lia|]. destruct (n <=? 65535); lia. Qed.
Lemma hdr_ext_le n : 2 <= hdr_ext n <= 6.
Proof. unfold hdr_ext. destruct (_ || _); [lia|]. destruct (n <=? 255); [lia|]. destruct (n <=? 65535); lia. Qed.
Lemma hdr_cont_le n : 1 <= hdr_cont n <= 5.  Proof. unfold hdr_cont. destruct (n <=? 15); [lia|]. destruct (n <=? 65535); lia. Qed.
Lemma w_u64_le v : 1 <= w_u64 v <= 9.
Proof. unfold w_u64. destruct (v <=? 127); [lia|]. destruct (v <=? 255); [lia|]. destruct (v <=? 65535); [lia|]. destruct (v <=? 4294967295); lia. Qed.
Lemma w_i64_le v : 1 <= w_i64 v <= 9.
Proof.
  unfold w_i64. destruct (0 <=? v); [apply w_u64_le|]. destruct (-32 <=? v); [lia|]. destruct (-128 <=? v); [lia|].
  destruct (-32768 <=? v); [lia|]. destruct (-2147483648 <=? v); lia.
Qed.
Lemma w_ts_le s : 6 <= w_ts s <= 15.  Proof. unfold w_ts. destruct (s <? 2 ^ 32); [lia|]. destruct (s <? 2 ^ 34); lia. Qed.
(* [comment removed for export] *)
Lemma hdr_str_min n h : 0 <= n -> (n <= 31 /\ h = 1) \/ (n <= 255 /\ h = 2) \/ (n <= 65535 /\ h = 3) \/ h = 5 -> hdr_str n <= h.
Proof.
  intros Hn H. unfold hdr_str.
  destruct (n <=? 31) eqn:E1; [apply Z.leb_le in E1|apply Z.leb_gt in E1]; [lia|].
  destruct (n <=? 255) eqn:E2; [apply Z.leb_le in E2|apply Z.leb_gt in E2]; [lia|].
  destruct (n <=? 65535) eqn:E3; [apply Z.leb_le in E3|apply Z.leb_gt in E3]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record enc : Type := ENC { en_b : Z; en_k : Z; en_n : Z; en_depth : Z }.
Definition enc0 : enc := ENC 0 0 0 0.        (* [comment removed for export] *)
Definition ecap (k : Z) : Z := if k =? 0 then 0 else 2 ^ (k - 1).
Definition enc_own (en : enc) : list (Z * Z) := if en_k en =? 0 then [] else [(en_b en, ESZ * ecap (en_k en))].
(* [comment removed for export] *)
Definition enc_push (en : enc) (b' k' : Z) : enc := ENC b' k' (en_n en + 1) (en_depth en + 1).
Definition enc_end_pop (en : enc) : enc := ENC (en_b en) (en_k en) (en_n en - 1) (en_depth en - 1).
Definition enc_end_keep (en : enc) : enc := ENC (en_b en) (en_k en) (en_n en) (en_depth en - 1).
(* [comment removed for export] *)
Definition push_law (en : enc) (b' k' : Z) : Prop :=
  (en_n en < ecap (en_k en) /\ b' = en_b en /\ k' = en_k en) \/ (en_n en = ecap (en_k en) /\ k' = en_k en + 1).

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable vp_adaptor : Z.     (* [comment removed for export] *)

Definition enc_at (M : word -> option byte) (ov osk : Z) (en : enc) : Prop :=
  L5.u64_at segs M ov (ne_vt E) /\ L5.u64_at segs M (ov + 8) osk /\ L5.u32_at segs M (ov + 16) MAX_DEPTH
  /\ L5.u64_at segs M (ov + 24) (en_b en)
  /\ L5.u64_at segs M (ov + 32) (en_b en + ESZ * en_n en)
  /\ L5.u64_at segs M (ov + 40) (en_b en + ESZ * ecap (en_k en))
  /\ L5.u32_at segs M (ov + 48) (en_depth en)
  /\ L5.defined M ov ESIZE /\ acc M ov ESIZE
  /\ 0 <= en_k en <= EKMAX /\ 0 <= en_depth en <= en_n en /\ en_n en <= ecap (en_k en)
  /\ (en_k en = 0 -> en_b en = 0)
  /\ (0 < en_k en ->
        en_b en mod 8 = 0 /\ L5.defined M (en_b en) (ESZ * ecap (en_k en)) /\ block_range L (en_b en) (ESZ * ecap (en_k en))
        /\ acc M (en_b en) (ESZ * en_n en) /\ ann M (en_b en) (ESZ * en_n en) (ESZ * ecap (en_k en))).
(* [comment removed for export] *)
Definition enc_W (ov : Z) : list L5.range := [(ov + 24, 32)].
(* [comment removed for export] *)
Definition pot_estack (k : Z) : credit :=
  (hl_k_per_malloc L * (EKMAX - k), ESZ * (2 ^ EKMAX - 2 ^ k) + (EKMAX - k) * hl_b_overhead L).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.
Definition content_at (M : word -> option byte) (d : Z) (bs : list Z) : Prop := L5.bytes_at segs M d bs /\ bytes_ok bs.
Definition kcontent (M : word -> option byte) (o : Z) (x : PM.vstr) (bs : list Z) : Prop :=
  content_at M (PM.vs_data o x) bs /\ Z.of_nat (length bs) = PM.vs_size x.
(* [comment removed for export] *)
Definition ascii (bs : list Z) : Prop := Forall (fun b => 0 <= b < 128) bs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record aest : Type := AEST { ae_a : PQM.ast; ae_kbb : list Z; ae_e : enc; ae_s : NESK.sink }.
(* [comment removed for export] *)
Definition ndest (lv : list PQM.alvl) : Z := Z.of_nat (length (List.filter (fun x => PQM.lv_t x =? 0) lv)) - 1.
Definition nlv (st : aest) : Z := PQM.nlv (ae_a st).
Definition kbsize (st : aest) : Z := PQM.kbsize (ae_a st).
Definition zsize (st : aest) : Z := NESK.sk_z (ae_s st).
Definition esize (st : aest) : Z := en_n (ae_e st).
Definition edepth (st : aest) : Z := en_depth (ae_e st).
(* [comment removed for export] *)
Definition phi (st : aest) : Z := zsize st + kbsize st.

Definition ae_at (M : word -> option byte) (oa ov osk : Z) (st : aest) : Prop :=
  PQM.adaptor_at segs A acc ann vp_adaptor M oa ov (ae_a st)
  /\ kcontent M (oa + PQM.AOFF_KB) (PQM.a_kb (ae_a st)) (ae_kbb st)
  /\ enc_at M ov osk (ae_e st)
  /\ NESK.sink_at segs L acc ann NESK.PME M osk (ae_s st).
(* [comment removed for export] *)
Definition ae_ok (st : aest) : Prop :=
  PQM.adaptor_ok (ae_a st) /\ utf8_valid (ae_kbb st) = true /\ en_depth (ae_e st) = ndest (PQM.a_lv (ae_a st)).
Definition aeown (st : aest) : list (Z * Z) := PQM.aown (ae_a st) ++ enc_own (ae_e st) ++ NESK.sink_own (ae_s st).
(* [comment removed for export] *)
Definition ae_W (oa ov osk oec : Z) : list L5.range :=
  PQM.adaptor_W oa ++ enc_W ov ++ [(osk, 24); (oec, 16)] ++ PMSP.err_W A.
Definition pot_ae (st : aest) : credit :=
  PM.credit_add (PQM.pot_adaptor L (ae_a st)) (PM.credit_add (pot_estack (en_k (ae_e st))) (NESK.sink_pot NESK.PME (NESK.sk_c (ae_s st)))).

(* [comment removed for export] *)
Definition ec_state (M : word -> option byte) (oec : Z) (b : bool) (cat : Z) : Prop :=
  if b then exists v, 1 <= v <= 64 /\ PMSP.ec_at segs M oec v (pa_errcat_obj A) else PMSP.ec_at segs M oec 0 cat.

End Model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition oacct (n : Z) (s : PQM.mpst) (st : aest) (sm : PM.strm) : Prop :=
  phi st + 6 * nlv st + 8 * PM.unread (PQM.p_src s) sm <= 8 * n + 6 /\ 0 <= n < 2 ^ 26.
(* [comment removed for export] *)
Definition oacct_d (d n : Z) (s : PQM.mpst) (st : aest) (sm : PM.strm) : Prop :=
  phi st + 6 * nlv st + 8 * PM.unread (PQM.p_src s) sm + d <= 8 * n + 6 /\ 0 <= n < 2 ^ 26.

Lemma oacct_d0 n s st sm : oacct n s st sm <-> oacct_d 0 n s st sm.
Proof. unfold oacct, oacct_d. lia. Qed.
(* [comment removed for export] *)
Lemma oacct_consume d n s s' st sm sm' c :
  oacct_d d n s st sm -> 0 <= c -> PM.unread (PQM.p_src s') sm' <= PM.unread (PQM.p_src s) sm - c -> oacct_d (d + 8 * c) n s' st sm'.
Proof. unfold oacct_d. lia. Qed.
(* [comment removed for export] *)
Lemma oacct_val d n s st st' sm :
  oacct_d d n s st sm -> nlv st' = nlv st -> phi st' <= phi st + d -> oacct n s st' sm.
Proof. unfold oacct, oacct_d. lia. Qed.
(* [comment removed for export] *)
Lemma oacct_push d dphi n s st st' sm :
  oacct_d d n s st sm -> nlv st' = nlv st + 1 -> phi st' <= phi st + dphi -> dphi + 6 <= d -> oacct n s st' sm.
Proof. unfold oacct, oacct_d. lia. Qed.
(* [comment removed for export] *)
Lemma oacct_pop d n s st st' sm :
  oacct_d d n s st sm -> nlv st' = nlv st - 1 -> phi st' <= phi st + 6 + d -> oacct n s st' sm.
Proof. unfold oacct, oacct_d. lia. Qed.
(* [comment removed for export] *)
Lemma oacct_bounds d n s st sm :
  oacct_d d n s st sm -> 0 <= PM.unread (PQM.p_src s) sm -> 0 <= kbsize st -> 0 <= zsize st -> 1 <= nlv st ->
  zsize st + d <= NESK.SMZ /\ phi st + d <= 8 * n.
Proof. unfold oacct_d, phi, NESK.SMZ. intros. change (2 ^ 26) with 67108864 in *. change (2 ^ 29) with 536870912. lia. Qed.
(* [comment removed for export] *)
Lemma oacct_pop_room n s st sm :
  oacct n s st sm -> 0 <= PM.unread (PQM.p_src s) sm -> 2 <= nlv st -> phi st + 6 <= NESK.SMZ.
Proof. unfold oacct, NESK.SMZ. intros. change (2 ^ 26) with 67108864 in *. change (2 ^ 29) with 536870912. lia. Qed.
Lemma oacct_val_room d n s st sm :
  oacct_d d n s st sm -> 0 <= PM.unread (PQM.p_src s) sm -> 0 <= kbsize st -> 1 <= nlv st -> zsize st + d <= NESK.SMZ.
Proof. unfold oacct_d, phi, NESK.SMZ. intros. change (2 ^ 26) with 67108864 in *. change (2 ^ 29) with 536870912. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cpl (s : PQM.mpst) (st : aest) : Prop := PQM.cpl s (ae_a st).
Definition bal (st : aest) : Prop := esize st = edepth st.
Definition ebound (st : aest) : Prop := esize st <= MAX_DEPTH.

Lemma ndest_nonneg_shape lv : PQM.lv_shape lv -> 0 <= ndest lv.
Proof.
  intros (L1 & _ & R0 & _). unfold ndest. destruct lv as [|x t]; [cbn in L1; lia|]. cbn [nth] in R0. subst x.
  cbn [List.filter PQM.lv_t PQM.lv_root Z.eqb]. cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma filter_length_le {T} (f : T -> bool) (l : list T) : (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x t IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.
Lemma ndest_le lv : ndest lv <= Z.of_nat (length lv) - 1.
Proof. unfold ndest. pose proof (filter_length_le (fun x => PQM.lv_t x =? 0) lv). lia. Qed.
(* [comment removed for export] *)
Lemma edepth_room st : ae_ok st -> nlv st <= MAX_DEPTH -> edepth st + 1 <= MAX_DEPTH.
Proof.
  intros (_ & _ & CP) Hn. unfold edepth, nlv, PQM.nlv, MAX_DEPTH in *. rewrite CP. pose proof (ndest_le (PQM.a_lv (ae_a st))). lia.
Qed.
(* [comment removed for export] *)
Lemma ecap_room k n : 0 <= k <= EKMAX -> n <= ecap k -> n <= MAX_DEPTH -> n = ecap k -> k + 1 <= EKMAX.
Proof.
  unfold EKMAX, MAX_DEPTH, PQM.MAX_DEPTH, ecap. intros Hk _ Hn ->.
  destruct (k =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|apply Z.eqb_neq in E0].
  destruct (Z_lt_le_dec (k + 1) 13) as [|Hge]; [lia|exfalso].
  assert (k = 12) by lia. subst k. cbn in Hn. lia.
Qed.
Lemma ecap_next k : 0 <= k -> ecap (k + 1) = (if k =? 0 then 1 else 2 * ecap k).
Proof.
  intros Hk. unfold ecap. replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; subst; reflexivity|apply Z.eqb_neq in E].
  replace (k + 1 - 1) with (k - 1 + 1) by lia. rewrite Z.pow_add_r, Z.pow_1_r; lia.
Qed.
(* [comment removed for export] *)
Lemma ebound_of_bal st : ae_ok st -> bal st -> nlv st <= MAX_DEPTH + 1 -> ebound st.
Proof.
  intros (_ & _ & CP) B Hn. unfold ebound, bal, esize, edepth, nlv, PQM.nlv, MAX_DEPTH in *. rewrite B, CP.
  pose proof (ndest_le (PQM.a_lv (ae_a st))). lia.
Qed.

(* [comment removed for export] *)
Lemma ndest_app_dest lv : ndest (lv ++ [PQM.AL 0 1 1]) = ndest lv + 1 /\ ndest (lv ++ [PQM.AL 0 2 0]) = ndest lv + 1.
Proof. unfold ndest. rewrite !List.filter_app, !List.length_app. cbn. lia. Qed.
Lemma ndest_app_buf lv k eo : ndest (lv ++ [PQM.AL 1 k eo]) = ndest lv.
Proof. unfold ndest. rewrite List.filter_app, List.length_app. cbn. lia. Qed.
Lemma ndest_app x lv : ndest (lv ++ [x]) = ndest lv + (if PQM.lv_t x =? 0 then 1 else 0).
Proof. unfold ndest. rewrite List.filter_app, List.length_app. cbn. destruct (PQM.lv_t x =? 0); cbn; lia. Qed.
Lemma ndest_removelast lv x : lv <> [] -> last lv PQM.lv_root = x -> ndest (removelast lv) = ndest lv - (if PQM.lv_t x =? 0 then 1 else 0).
Proof.
  intros Hne Hl. rewrite (app_removelast_last PQM.lv_root Hne) at 2. rewrite Hl, ndest_app. lia.
Qed.
(* [comment removed for export] *)
Lemma ndest_kinds lv lv' : List.map PQM.lv_t lv = List.map PQM.lv_t lv' -> ndest lv = ndest lv'.
Proof.
  intros H. unfold ndest. do 2 f_equal.
  revert lv' H. induction lv as [|x t IH]; intros [|y u] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Ht. cbn [List.filter]. rewrite Hx. specialize (IH u Ht). cbn in IH |- *.
  destruct (PQM.lv_t y =? 0); cbn; [f_equal|]; exact IH.
Qed.

(* [comment removed for export] *)
Lemma ndest_head_nonneg l : l <> [] -> nth 0 l PQM.lv_root = PQM.lv_root -> 0 <= ndest l.
Proof.
  intros Hne H0. unfold ndest. destruct l as [|y u]; [congruence|]. cbn [nth] in H0. subst y.
  cbn [List.filter PQM.lv_t PQM.lv_root Z.eqb]. cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma ndest_top_dest lv x :
  (2 <= length lv)%nat -> nth 0 lv PQM.lv_root = PQM.lv_root -> last lv PQM.lv_root = x -> PQM.lv_t x = 0 -> 1 <= ndest lv.
Proof.
  intros Hl H0 Hx Ht.
  assert (Hne : lv <> []) by (destruct lv; cbn in Hl; [lia|congruence]).
  pose proof (ndest_removelast lv x Hne Hx) as R. rewrite Ht in R. cbn in R.
  assert (Hr : removelast lv <> [] /\ nth 0 (removelast lv) PQM.lv_root = PQM.lv_root).
  { destruct lv as [|y [|z u]]; cbn in Hl; [lia|lia|]. cbn [nth] in H0. subst y. split; [cbn; congruence|reflexivity]. }
  destruct Hr as [Hr1 Hr2]. pose proof (ndest_head_nonneg (removelast lv) Hr1 Hr2). lia.
Qed.
Lemma eend_room st : ae_ok st -> 1 <= ndest (PQM.a_lv (ae_a st)) -> 1 <= edepth st.
Proof. intros (_ & _ & CP) H. unfold edepth. rewrite CP. exact H. Qed.

End NEM.

End NemModel.
Module NemSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module NECS.
Import NEM.

Definition ENC_H : Z := 4.
Definition ENC_HS : Z := 7.
(* [comment removed for export] *)
Inductive eend : Type := EPop | EKeep.
Definition enc_end (en : enc) (o : eend) : enc := match o with EPop => enc_end_pop en | EKeep => enc_end_keep en end.
(* [comment removed for export] *)
Record eargs : Type := EA { ea_tag : Z; ea_val : Z; ea_n : Z; ea_bs : list Z }.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AQ : pq_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation enc_at := (NEM.enc_at segs E L T3 T4).
Abbreviation sink_at := (NESK.sink_at segs L T3 T4 P).
Abbreviation ec_state := (NEM.ec_state segs A).
Abbreviation err_ok := (PQST.err_ok segs A AQ).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).

(* [comment removed for export] *)
Definition pot_enc (en : enc) (k : NESK.sink) : credit := PM.credit_add (pot_estack L (en_k en)) (NESK.sink_pot P (NESK.sk_c k)).
Definition eown (en : enc) (k : NESK.sink) : list (Z * Z) := enc_own en ++ NESK.sink_own k.
(* [comment removed for export] *)
Definition W_enc (ov osk oec : Z) : list L5.range := enc_W ov ++ [(osk, 24); (oec, 16)] ++ PMSP.err_W A.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition view_ok (M : word -> option byte) (sp ov : Z) (LBX : list (Z * Z)) (p d n : Z) : Prop :=
  L5.u64_at segs M p d /\ L5.u64_at segs M (p + 8) n /\ 0 <= n < 2 ^ 29 /\ L5.defined M d n   (* [comment removed for export] *)
  /\ (n = 0 \/ PGS.in_blk LBX d n \/ (sp <= d /\ d + n <= ov /\ 4096 <= d))
  /\ 0 <= d /\ d + n <= 2 ^ 47.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eslot_spec (pc h : Z)
           (args : eargs -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> Z -> list (Z * Z) -> Prop)
           (pre : eargs -> enc -> NESK.sink -> Prop)
           (step : eargs -> enc -> NESK.sink -> bool -> enc -> NESK.sink -> bool -> Prop) : Prop :=
  NESK.sp_mode P ->
  forall (a : eargs) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat : Z) (en : enc) (k : NESK.sink) (b e : bool),
    hi_heap HI (eown en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h ->
    getr R 10%bv = Z_to_bv 64 ov -> args a R M sp ov oec LBX ->
    sp <= ov -> ov + 56 <= hl_sptop L -> ov mod 8 = 0 -> sp <= osk -> osk + 24 <= hl_sptop L -> osk mod 8 = 0 ->
    sp <= oec -> oec + 16 <= hl_sptop L -> oec mod 8 = 0 -> oec + 16 <= ov -> ov + 56 <= osk ->       (* [comment removed for export] *)
    enc_at M ov osk en -> sink_at M osk k -> ec_state M oec b cat -> PMST.base_ok segs A M -> err_ok M e ->
    pre a en k ->
    PMSP.credit_le (pot_enc en k) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
            (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_at M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok segs A M' -> err_ok M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> step a en k b en' k' b' ->
        L5C.hpres L LBX sp (pm_scr h) (W_enc ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (pot_enc en k) (pot_enc en' k') ->
        model_but_vm model model' -> hi_heap HI (eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eargs_t3 (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 13%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition eargs_bool (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  (getr R 11%bv = Z_to_bv 64 0 \/ getr R 11%bv = Z_to_bv 64 1) /\ getr R 14%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition eargs_u64 (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 (ea_val a) /\ 0 <= ea_val a < 2 ^ 64
  /\ getr R 12%bv = Z_to_bv 64 (ea_tag a) /\ (ea_tag a = TAG_NONE \/ ea_tag a = TAG_ESEC) /\ getr R 14%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition eargs_i64 (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 (ea_val a) /\ 0 <= ea_val a < 2 ^ 64 /\ getr R 12%bv = Z_to_bv 64 TAG_NONE /\ getr R 14%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition eargs_dbl (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 13%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eargs_str (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  exists p d, getr R 11%bv = Z_to_bv 64 p /\ sp <= p /\ p + 16 <= ov /\ view_ok M sp ov LBX p d (ea_n a)
  /\ getr R 12%bv = Z_to_bv 64 (ea_tag a) /\ (ea_tag a = TAG_NONE \/ ea_tag a = TAG_ENANO) /\ getr R 14%bv = Z_to_bv 64 oec
  /\ (ea_tag a = TAG_NONE -> L5.bytes_at segs M d (ea_bs a) /\ Z.of_nat (length (ea_bs a)) = ea_n a /\ utf8_valid (ea_bs a) = true /\ bytes_ok (ea_bs a))
  /\ (ea_tag a = TAG_ENANO -> ea_n a <= 31).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition eargs_key (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  exists p d, getr R 11%bv = Z_to_bv 64 p /\ sp <= p /\ p + 16 <= ov /\ view_ok M sp ov LBX p d (ea_n a)
  /\ getr R 13%bv = Z_to_bv 64 oec
  /\ L5.bytes_at segs M d (ea_bs a) /\ Z.of_nat (length (ea_bs a)) = ea_n a /\ utf8_valid (ea_bs a) = true /\ bytes_ok (ea_bs a).
(* [comment removed for export] *)
Definition eargs_bstr (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  exists p d, getr R 11%bv = Z_to_bv 64 p /\ sp <= p /\ p + 16 <= ov /\ view_ok M sp ov LBX p d (ea_n a)
  /\ getr R 14%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition eargs_len (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 (ea_val a) /\ 0 <= ea_val a < 2 ^ 64 /\ getr R 14%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition eargs_end (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 12%bv = Z_to_bv 64 oec.
Definition eargs_none (a : eargs) (R : bvmap 5 word) (M : word -> option byte) (sp ov oec : Z) (LBX : list (Z * Z)) : Prop := True.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pre_w (wmax : Z) (a : eargs) (en : enc) (k : NESK.sink) : Prop := NESK.sk_z k + wmax <= NESK.SMZ.
(* [comment removed for export] *)
Definition pre_str5 (a : eargs) (en : enc) (k : NESK.sink) : Prop := NESK.sk_z k + ea_n a + 5 <= NESK.SMZ.
Definition pre_view (a : eargs) (en : enc) (k : NESK.sink) : Prop := NESK.sk_z k + ea_n a + 6 <= NESK.SMZ.
(* [comment removed for export] *)
Definition pre_begin (a : eargs) (en : enc) (k : NESK.sink) : Prop :=
  NESK.sk_z k + 5 <= NESK.SMZ /\ en_n en <= MAX_DEPTH /\ en_depth en + 1 <= MAX_DEPTH.
(* [comment removed for export] *)
Definition pre_end (a : eargs) (en : enc) (k : NESK.sink) : Prop := 1 <= en_depth en.
Definition pre_none (a : eargs) (en : enc) (k : NESK.sink) : Prop := True.

(* [comment removed for export] *)
Definition step_w (wmax : Z) (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + wmax /\ b' = b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition step_u64 (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + (if ea_tag a =? TAG_ESEC then 15 else w_u64 (ea_val a)) /\ b' = b.
(* [comment removed for export] *)
Definition sval (v : Z) : Z := if v <? 2 ^ 63 then v else v - 2 ^ 64.
Definition step_i64 (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + w_i64 (sval (ea_val a)) /\ b' = b.
(* [comment removed for export] *)
Definition step_str (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + (if ea_tag a =? TAG_ENANO then Z.max (ea_n a + 5) 15 else ea_n a + 5) /\ (ea_tag a = TAG_NONE -> b' = b).
Definition pre_vstr (a : eargs) (en : enc) (k : NESK.sink) : Prop := pre_str5 a en k /\ (ea_tag a = TAG_ENANO -> NESK.sk_z k + 15 <= NESK.SMZ).
Definition step_key (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + hdr_str (ea_n a) + ea_n a /\ b' = b.
(* [comment removed for export] *)
Definition pre_u64 (a : eargs) (en : enc) (k : NESK.sink) : Prop :=
  NESK.sk_z k + (if ea_tag a =? TAG_ESEC then 15 else w_u64 (ea_val a)) <= NESK.SMZ.
Definition pre_i64 (a : eargs) (en : enc) (k : NESK.sink) : Prop := NESK.sk_z k + w_i64 (sval (ea_val a)) <= NESK.SMZ.
Definition pre_key (a : eargs) (en : enc) (k : NESK.sink) : Prop := NESK.sk_z k + hdr_str (ea_n a) + ea_n a <= NESK.SMZ.
Definition step_view (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + ea_n a + 6 /\ b' = b.
(* [comment removed for export] *)
Definition step_begin (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  (exists b1 k1, push_law en b1 k1 /\ en' = enc_push en b1 k1) /\ NESK.sk_z k <= NESK.sk_z k' <= NESK.sk_z k + hdr_cont (ea_val a) /\ b' = b.
(* [comment removed for export] *)
Definition step_end (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  exists o, en' = enc_end en o /\ k' = k /\ (o = EPop -> b' = b) /\ (o = EKeep -> b' = true).
Definition step_none (a : eargs) (en : enc) (k : NESK.sink) (b : bool) (en' : enc) (k' : NESK.sink) (b' : bool) : Prop :=
  en' = en /\ k' = k /\ b' = b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition v_null_spec : Prop := eslot_spec (ne_null E) ENC_H eargs_t3 (pre_w 1) (step_w 1).
Definition v_bool_spec : Prop := eslot_spec (ne_bool E) ENC_H eargs_bool (pre_w 1) (step_w 1).
Definition v_uint64_spec : Prop := eslot_spec (ne_uint64 E) ENC_H eargs_u64 pre_u64 step_u64.
Definition v_int64_spec : Prop := eslot_spec (ne_int64 E) ENC_H eargs_i64 pre_i64 step_i64.
Definition v_double_spec : Prop := eslot_spec (ne_double E) ENC_H eargs_dbl (pre_w 9) (step_w 9).
Definition v_string_spec : Prop := eslot_spec (ne_string E) ENC_HS eargs_str pre_vstr step_str.   (* [comment removed for export] *)
Definition v_key_spec : Prop := eslot_spec (ne_key E) ENC_HS eargs_key pre_key step_key.
Definition v_bstr_tag_spec : Prop := eslot_spec (ne_bstr_tag E) ENC_H eargs_bstr pre_view step_view.
Definition v_bstr_raw_spec : Prop := eslot_spec (ne_bstr_raw E) ENC_H eargs_bstr pre_view step_view.
Definition v_begin_arr_spec : Prop := eslot_spec (ne_begin_arr_len E) ENC_H eargs_len pre_begin step_begin.
Definition v_begin_obj_spec : Prop := eslot_spec (ne_begin_obj_len E) ENC_H eargs_len pre_begin step_begin.
Definition v_end_arr_spec : Prop := eslot_spec (ne_end_arr E) ENC_H eargs_end pre_end step_end.
Definition v_end_obj_spec : Prop := eslot_spec (ne_end_obj E) ENC_H eargs_end pre_end step_end.
Definition v_flush_spec : Prop := eslot_spec (ne_flush E) 0 eargs_none pre_none step_none.

(* [comment removed for export] *)
Record enc_ok : Prop := ENCOK {
  eo_null : v_null_spec; eo_bool : v_bool_spec; eo_uint64 : v_uint64_spec; eo_int64 : v_int64_spec; eo_double : v_double_spec;
  eo_string : v_string_spec; eo_key : v_key_spec; eo_bstr_tag : v_bstr_tag_spec; eo_bstr_raw : v_bstr_raw_spec;
  eo_begin_arr : v_begin_arr_spec; eo_begin_obj : v_begin_obj_spec; eo_end_arr : v_end_arr_spec; eo_end_obj : v_end_obj_spec;
  eo_flush : v_flush_spec }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ntb_spec (W pc : Z) : Prop :=
  NESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r q osk : Z) (k : NESK.sink),
    hi_heap HI (NESK.sink_own k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 2 ->
    getr R 11%bv = Z_to_bv 64 q -> L5.u64_at segs M q osk -> sp <= q -> q + 8 <= hl_sptop L -> q mod 8 = 0 -> (q + 8 <= osk \/ osk + 24 <= q) ->
    sp <= osk -> osk + 24 <= hl_sptop L -> osk mod 8 = 0 -> sink_at M osk k ->
    NESK.sk_z k + W <= NESK.SMZ ->
    PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (k' : NESK.sink) (cr' : credit),
        regs_preserved R R' ->
        sink_at M' osk k' -> NESK.sk_z k' = NESK.sk_z k + W ->
        L5C.hpres L LBX sp (pm_scr 2) [(osk, 24)] M M' ->
        PMSP.credit_keep cr cr' (NESK.sink_pot P (NESK.sk_c k)) (NESK.sink_pot P (NESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (NESK.sink_own k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition write_timestamp_spec : Prop :=
  NESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r ov osk : Z) (en : enc) (k : NESK.sink),
    hi_heap HI (eown en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 3 ->
    getr R 10%bv = Z_to_bv 64 ov ->
    sp <= ov -> ov + 56 <= hl_sptop L -> ov mod 8 = 0 -> sp <= osk -> osk + 24 <= hl_sptop L -> osk mod 8 = 0 -> ov + 56 <= osk ->
    enc_at M ov osk en -> sink_at M osk k ->
    NESK.sk_z k + 15 <= NESK.SMZ ->
    PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (k' : NESK.sink) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en -> sink_at M' osk k' -> NESK.sk_z k + 6 <= NESK.sk_z k' <= NESK.sk_z k + 15 ->
        L5C.hpres L LBX sp (pm_scr 3) [(osk, 24)] M M' ->
        PMSP.credit_keep cr cr' (NESK.sink_pot P (NESK.sk_c k)) (NESK.sink_pot P (NESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (eown en k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (ne_write_timestamp E) M model) K.

(* [comment removed for export] *)
Definition wsv_spec : Prop :=
  NESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r ov osk p d n : Z) (bs : list Z) (en : enc) (k : NESK.sink),
    hi_heap HI (eown en k ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 3 ->
    getr R 10%bv = Z_to_bv 64 ov -> getr R 11%bv = Z_to_bv 64 p -> sp <= p -> p + 16 <= ov -> view_ok M sp ov LBX p d n ->
    L5.bytes_at segs M d bs -> Z.of_nat (length bs) = n -> utf8_valid bs = true -> bytes_ok bs ->
    sp <= ov -> ov + 56 <= hl_sptop L -> ov mod 8 = 0 -> sp <= osk -> osk + 24 <= hl_sptop L -> osk mod 8 = 0 -> ov + 56 <= osk ->
    enc_at M ov osk en -> sink_at M osk k -> PMST.base_ok segs A M ->
    NESK.sk_z k + hdr_str n + n <= NESK.SMZ ->   (* [comment removed for export] *)
    PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (k' : NESK.sink) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en -> sink_at M' osk k' -> NESK.sk_z k' = NESK.sk_z k + hdr_str n + n ->
        L5C.hpres L LBX sp (pm_scr 3) [(osk, 24)] M M' ->
        PMSP.credit_keep cr cr' (NESK.sink_pot P (NESK.sk_c k)) (NESK.sink_pot P (NESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (eown en k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (ne_write_string_value E) M model) K.
(* [comment removed for export] *)

End Specs.
End NECS.

End NemSpecs.
Module PnAdStr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQAS.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gcount (cap need : Z) : Z := Z.lor (Z.max (2 * cap) need) 7 + 1.

Lemma lor7_low r : 0 <= r < 8 -> Z.lor r 7 = 7.
Proof.
  intros H. assert (E : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia.
  repeat (destruct E as [->|E]; [reflexivity|]). subst r. reflexivity.
Qed.

Lemma lor7 x : 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof.
  intros Hx. rewrite (Z.div_mod x 8) at 1 by lia.
  assert (Hr : 0 <= x mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (E1 : 8 * (x / 8) + x mod 8 = Z.lor (8 * (x / 8)) (x mod 8)).
  { rewrite <- Z.lxor_lor.
    - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
      apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      replace (8 * (x / 8)) with (x / 8 * 2 ^ 3) by (change (2 ^ 3) with 8; lia).
      destruct (Z.lt_ge_cases i 3) as [Lo|Hi3].
      + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      + replace (Z.testbit (x mod 8) i) with false; [apply andb_false_r|].
        symmetry. change 8 with (2 ^ 3). rewrite Z.mod_pow2_bits_high by lia. reflexivity.
    - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      replace (8 * (x / 8)) with (x / 8 * 2 ^ 3) by (change (2 ^ 3) with 8; lia).
      destruct (Z.lt_ge_cases i 3) as [Lo|Hi3].
      + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      + replace (Z.testbit (x mod 8) i) with false; [apply andb_false_r|].
        symmetry. change 8 with (2 ^ 3). rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite E1, <- Z.lor_assoc, (lor7_low (x mod 8) Hr).
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (8 * (x / 8)) with (x / 8 * 2 ^ 3) by (change (2 ^ 3) with 8; lia).
    destruct (Z.lt_ge_cases i 3) as [Lo|Hi3].
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + replace (Z.testbit 7 i) with false; [apply andb_false_r|].
      symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_high. lia.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (8 * (x / 8)) with (x / 8 * 2 ^ 3) by (change (2 ^ 3) with 8; lia).
    destruct (Z.lt_ge_cases i 3) as [Lo|Hi3].
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + replace (Z.testbit 7 i) with false; [apply andb_false_r|].
      symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_high. lia.
Qed.

Lemma gcount_eq cap need : 0 <= cap -> 0 <= need -> gcount cap need = 8 * (Z.max (2 * cap) need / 8) + 8.
Proof. intros H1 H2. unfold gcount. rewrite lor7 by lia. lia. Qed.

(* [comment removed for export] *)
Lemma gcount_facts cap need : 0 <= cap -> 0 <= need ->
  gcount cap need mod 8 = 0 /\ Z.max (2 * cap) need < gcount cap need <= Z.max (2 * cap) need + 8.
Proof.
  intros H1 H2. rewrite gcount_eq by lia.
  pose proof (Z.mod_pos_bound (Z.max (2 * cap) need) 8 ltac:(lia)) as B.
  pose proof (Z.div_mod (Z.max (2 * cap) need) 8 ltac:(lia)) as D.
  split; [|lia]. replace (8 * (Z.max (2 * cap) need / 8) + 8) with ((Z.max (2 * cap) need / 8 + 1) * 8) by lia.
  apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma ks_grow SM s g need n' p' :
  PQM.ks_ok SM s g -> PM.vs_cap s < need -> need <= SM -> 0 <= n' <= SM -> n' <= need ->
  let c' := gcount (PM.vs_cap s) need in
  PQM.ks_ok SM (PM.VLong c' n' p') (g + 1) /\ 2 * PQM.ks_alloc s <= c' /\ 48 <= c' /\ c' <= 2 * SM + 8 /\ c' mod 8 = 0
  /\ n' < c' /\ 26 <= c' <= PQM.KCAP /\ c' mod 2 = 0 /\ g < PQM.GMAX.
Proof.
  intros (S0 & S1 & SS) Hcap Hneed Hn1 Hn2 c'.
  assert (Hcap0 : 22 <= PM.vs_cap s).
  { destruct s as [n0|c n0 p]; cbn [PM.vs_cap] in *; [lia|]. destruct SS as (G1 & G2 & _).
    pose proof (Z.pow_pos_nonneg 2 (g - 1) ltac:(lia)) as P. lia. }
  destruct (gcount_facts (PM.vs_cap s) need ltac:(lia) ltac:(lia)) as (M8 & LO & HI). fold c' in M8, LO, HI.
  assert (Hmax : Z.max (2 * PM.vs_cap s) need <= 2 * SM) by lia.
  assert (Hc'2 : c' <= 2 * SM + 8) by lia.
  assert (Hc'48 : 48 <= c') by lia.
  assert (H2c : 2 * PQM.ks_alloc s <= c').
  { destruct s as [n0|c n0 p]; cbn [PQM.ks_alloc PM.vs_cap] in *; [lia|].
    destruct SS as (_ & _ & C8 & _). 
    (* [comment removed for export] *)
    assert (E1 : exists q, c = 8 * q) by (exists (c / 8); pose proof (Z.div_mod c 8 ltac:(lia)); lia).
    assert (E2 : exists q, c' = 8 * q) by (exists (c' / 8); pose proof (Z.div_mod c' 8 ltac:(lia)); lia).
    destruct E1 as (q1 & ->). destruct E2 as (q2 & E2). rewrite E2 in *. lia. }
  assert (Hg : g < PQM.GMAX).
  { destruct s as [n0|c n0 p]; cbn [PQM.ks_alloc PM.vs_cap] in *; [subst g; unfold PQM.GMAX; lia|].
    destruct SS as (G1 & G2 & C8 & C2). unfold PQM.GMAX in *.
    destruct (Z_lt_le_dec g 28) as [|X]; [lia|]. exfalso.
    assert (P : 2 ^ 27 <= 2 ^ (g - 1)) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 27) with 134217728 in P. change (2 ^ 29) with 536870912 in S1. lia. }
  assert (Hg0 : 0 <= g) by (destruct s as [n0|c n0 p]; [lia| destruct SS; lia]).
  unfold PQM.KCAP. change (2 ^ 29) with 536870912 in S1. change (2 ^ 31) with 2147483648.
  split.
  - split; [cbn [PM.vs_size]; lia|]. split; [change (2 ^ 29) with 536870912; lia|].
    split; [unfold PQM.GMAX in *; lia|]. split; [|split; [exact M8| lia]].
    replace (g + 1 - 1) with g by lia.
    destruct s as [n0|c n0 p]; cbn [PQM.ks_alloc PM.vs_cap] in *.
    + subst g. change (48 * 2 ^ 0) with 48. lia.
    + destruct SS as (G1 & G2 & _).
      replace (2 ^ g) with (2 * 2 ^ (g - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). lia.
  - repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma pot_ks_grow L SM s g s' c' cr :
  0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> PQM.ks_alloc s' = c' -> 2 * PQM.ks_alloc s <= c' -> g < PQM.GMAX ->
  c' <= 2 * SM + 8 -> PQM.ks_alloc s <= SM -> PMSP.credit_le (PQM.pot_ks L SM s g) cr ->
  credit_ok L cr c' /\ PMSP.credit_keep cr (debit L cr c') (PQM.pot_ks L SM s g) (PQM.pot_ks L SM s' (g + 1)).
Proof.
  intros HK HB Ea H2 Hg Hc Ha (C1 & C2). unfold PQM.pot_ks in *. cbn [fst snd] in *. rewrite Ea.
  split; [unfold credit_ok; split; nia|]. unfold PMSP.credit_keep, debit. cbn [fst snd]. split; nia.
Qed.

(* [comment removed for export] *)
Lemma pot_ks_same L SM s g s' : PQM.ks_alloc s' = PQM.ks_alloc s -> PQM.pot_ks L SM s' g = PQM.pot_ks L SM s g.
Proof. intros E. unfold PQM.pot_ks. rewrite E. reflexivity. Qed.

Lemma ck_refl cr p : PMSP.credit_keep cr cr p p.
Proof. unfold PMSP.credit_keep. lia. Qed.
Lemma ck_trans cr1 cr2 cr3 p1 p2 p3 : PMSP.credit_keep cr1 cr2 p1 p2 -> PMSP.credit_keep cr2 cr3 p2 p3 -> PMSP.credit_keep cr1 cr3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.
Lemma cle_keep cr cr1 p p1 : PMSP.credit_le p cr -> PMSP.credit_keep cr cr1 p p1 -> PMSP.credit_le p1 cr1.
Proof. unfold PMSP.credit_le, PMSP.credit_keep. lia. Qed.
(* [comment removed for export] *)
Lemma ck_add_l cr cr' p q q' : PMSP.credit_keep cr cr' q q' -> PMSP.credit_keep cr cr' (PM.credit_add p q) (PM.credit_add p q').
Proof. unfold PMSP.credit_keep, PM.credit_add. cbn [fst snd]. lia. Qed.
Lemma ck_add_r cr cr' p p' q : PMSP.credit_keep cr cr' p p' -> PMSP.credit_keep cr cr' (PM.credit_add p q) (PM.credit_add p' q).
Proof. unfold PMSP.credit_keep, PM.credit_add. cbn [fst snd]. lia. Qed.
Lemma cle_add_l p q cr : 0 <= fst p -> 0 <= snd p -> PMSP.credit_le (PM.credit_add p q) cr -> PMSP.credit_le q cr.
Proof. unfold PMSP.credit_le, PM.credit_add. cbn [fst snd]. lia. Qed.
Lemma cle_add_r p q cr : 0 <= fst q -> 0 <= snd q -> PMSP.credit_le (PM.credit_add p q) cr -> PMSP.credit_le p cr.
Proof. unfold PMSP.credit_le, PM.credit_add. cbn [fst snd]. lia. Qed.

(* [comment removed for export] *)
Lemma pot_ks_nonneg L SM s g : 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> PQM.ks_ok SM s g ->
  0 <= fst (PQM.pot_ks L SM s g) /\ 0 <= snd (PQM.pot_ks L SM s g).
Proof.
  intros HK HB (S0 & S1 & SS). unfold PQM.pot_ks. cbn [fst snd].
  destruct s as [n|c n p]; cbn [PQM.ks_alloc] in *; unfold PQM.GMAX in *.
  - subst g. split; nia.
  - destruct SS as (G1 & G2 & C8 & C2). split; nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Abbreviation kstr_at := (PQM.kstr_at segs PMSP.T3).

(* [comment removed for export] *)
Definition opnew_spec_n (NMAX : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> credit_ok L cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp PMSP.OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp PMSP.OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R (pa_opnew A) M model) K.
(* [comment removed for export] *)
Definition NREQ : Z := 2 ^ 30 - 2 ^ 16.
Definition SMMAX : Z := 2 ^ 29 - 2 ^ 16.

(* [comment removed for export] *)
Definition pb_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o c sp r SM g : Z) (x : PM.vstr),
    hi_heap HI (PM.vs_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    WD.entry_scr A L R M sp r WD.PB_SCR ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 c -> 0 <= c < 256 ->
    kstr_at M o x -> PQM.ks_ok SM x g -> SM <= SMMAX -> PM.vs_size x < SM -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    PMSP.credit_le (PQM.pot_ks L SM x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
        regs_preserved R R' -> kstr_at M' o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + 1 ->
        L5C.hpres L LB sp WD.PB_SCR [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition src_ok (M : word -> option byte) (LB : list (Z * Z)) (sp o q n : Z) : Prop :=
  0 <= q /\ q + n < 2 ^ 47 /\ (forall i, 0 <= i < n -> L5C.kept L LB sp WD.PB_SCR [(o, 24)] (q + i))
  /\ exists bs, length bs = Z.to_nat n /\ rdn segs M (Z_to_bv 64 q) (length bs) = Some bs.

(* [comment removed for export] *)
Definition ins_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o q n sp r SM g : Z) (x : PM.vstr),
    hi_heap HI (PM.vs_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    WD.entry_scr A L R M sp r WD.PB_SCR ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x) ->
    getr R 12%bv = Z_to_bv 64 q -> getr R 13%bv = Z_to_bv 64 (q + n) -> getr R 14%bv = Z_to_bv 64 n ->
    0 <= n -> PM.vs_size x + n <= SM -> src_ok M LB sp o q n ->
    kstr_at M o x -> PQM.ks_ok SM x g -> SM <= SMMAX -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    PMSP.credit_le (PQM.pot_ks L SM x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
        regs_preserved R R' -> kstr_at M' o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
        L5C.hpres L LB sp WD.PB_SCR [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wd_sst : Type := (PM.vstr * Z)%type.
Definition wd_str_at (M : word -> option byte) (os : Z) (xg : wd_sst) : Prop :=
  kstr_at M os (fst xg) /\ PQM.ks_ok PQM.SMK (fst xg) (snd xg) /\ os mod 8 = 0.
Definition wd_str_own (xg : wd_sst) : list (Z * Z) := PM.vs_own (fst xg).
Definition wd_str_size (xg : wd_sst) : Z := PM.vs_size (fst xg) + (WD.STR_MAX - PQM.SMK).
Definition wd_str_pot (xg : wd_sst) : credit := PQM.pot_ks L PQM.SMK (fst xg) (snd xg).

Lemma wd_push_back_of (pc : Z) : pb_spec pc -> WD.push_back_spec segs A L HI wd_sst wd_str_at wd_str_own wd_str_size wd_str_pot pc.
Proof.
  intros PB fx R M model K LB cr os c sp r [x g] HH MOK K0 ENT R10 R11 Hc (SA & SO & S8) Hsz Hsp Hos BASE CR KONT.
  unfold wd_str_own, wd_str_size, wd_str_pot in *. cbn [fst snd] in *.
  apply (PB fx R M model K LB cr os c sp r PQM.SMK g x HH MOK K0 ENT R10 R11 Hc SA SO ltac:(unfold SMMAX, PQM.SMK; lia)
           ltac:(unfold WD.STR_MAX, PQM.SMK in *; lia) Hsp Hos S8 CR).
  intros fx' R' M' model' x' g' cr' RP SA' SO' Esz HP CK MB HH'.
  apply (KONT fx' R' M' model' (x', g') cr' RP); cbn [fst snd]; [| lia | exact HP | exact CK | exact MB | exact HH'].
  unfold wd_str_at. cbn [fst snd]. split; [exact SA'|]. split; [exact SO'| exact S8].
Qed.

End Specs.

End PQAS.

End PnAdStr.
Module PnMpModelFacts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnMpModelFacts () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc69OSSVerify5KrLib7Mh_01028NemModel3NEM@filter_length_leC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7existsbc69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6wd_sstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD>push_back_specC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notc69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF3dkrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powc69OSSVerify5KrLib7Mh_01028PnQModel3PQM9mstate_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7ms_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM6ms_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM6ms_idxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF6ag_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01i69OSSVerify5KrLib7Mh_01028PnQModel3PQM6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7mvec_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Peano2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_00907PmModel2PM8pow2_posC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF?mstate_at_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkrelc69OSSVerify5KrLib7Mh_01028PnQModel3PQM3PSZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7ms_rootC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00k69OSSVerify5KrLib7Mh_01024PnV84PQV82v802C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF;defined_dkrC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01024PnV84PQV82v800C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01024PnV84PQV82v801C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF8vs_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_srcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM8with_srcC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01028PnQModel3PQM4mpst01C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01028PnQModel3PQM4mpst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_tbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_bbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_sbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_skC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM:mparser_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_moreC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_doneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7p_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF?nullis_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF7dkr_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF<vstr_at_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF:v8_at_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF=mvec_at_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_SRCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM8OFF_MAXDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM6OFF_TBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM6OFF_BBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_STKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM9MAX_DEPTHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM5PSIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_tC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_kC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM5lv_eoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM3LSZC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lvec_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF=alvl_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lv_rootC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_keyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF<kstr_at_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF=lvec_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM8AOFF_KEYC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_KBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_LVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM9AOFF_DESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ASIZEC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_DVC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQMF.

(* [comment removed for export] *)
Definition dkr (M M' : word -> option byte) (a n : Z) : Prop :=
  forall i, a <= i < a + n -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Lemma dkr_agree M M' a n : L5C.agree_on M M' a n -> dkr M M' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) [] "h01Mh12M'h21ah31nh42AGh51Dh62Hih71ih81op;1p;4p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p4p70p1007]p4p771111110p8P1g008bR1p4p710p8g009@j10Tg009ej15Tg00:Cj12Tg00:fj16Tg00;Hj4>Tg00<Hj2;Tg00<dj2:Tg00=Aj29Tg00=]j28Tg00>8j21Tg00>^j17Tg00?@j34Tg00?Zj13TP1j6=Tg00@3j4<Tg00A7#0#0#0R1#0#0#0#5R0#2%51#2R1#6R2[R3g00A\R4f3R5f2R6f1R7f0R8C>1;581:56,98'8f6R91107O1%71R1542#3P2f71106R0O1A4281#3X82P8P9P0O1P5P6P7O2E=W5W6X74f4P5P6P7C<eW4X34X24X13X03P5P6P7P8O4X34W2X13W0o"). Qed.
Lemma dkr_sub M M' a n a' n' : dkr M M' a n -> a <= a' -> a' + n' <= a + n -> dkr M M' a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) [] "h01Mh12M'h24__x1h34__x2h44__x3h54__x4h64__x5h71ah82a'h91nh:2n'h;1Dh<2H1h=2H2h>2Hih?7__arithh@4__ffhA8__varmaphB5__withC1ip;1p;4p;2p;3p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p4p70p1007]p4p771111110p8P1p1008bp4p710p8g009@j13Tg009ej1CTg00:Cj1DTg00:fj1JTg00@3j4FTg00<Hj20Tg00<dj21Tg00=Aj2<Tg00=]j2:Tg00B:j16Tg00BYj25Tg00CBj37Tg00Ckj2ATg00DWj1VTg00E7j3ETg00EWj1UTg00F7j2BTg00FUj1TTg00G3j4=Tg00GQj1RTg00Goj1QTg00HZj24Tg00I=j1@Tg00Ibj3?Tg00JEj49Tg00>^j1LTg00K0j2KTg00KRj2ITg00Klj2MTg00?@j3NTg00LXj3HTg00M7j4OTg00Mij7PTg00NMj7GTg00O1j8STg00A\R1f1R0g00OUf0R2C9p=8P0g00P<R3g00P[R4P4g00Q;R5P2g00Q[FPp=2f2R6P3P4P4P5P0P2FGp=>f3R7P3P4P4P5P6P0P2GSp=;g00A7R3#3R8#3R9#3R:#3#3#3#C#D%C:#D#J[R:f5R;f4R<P7P6CF10<6117611;<R='010;21<2=':P<P0g00R;R=g00RgR>#6R?#6R@#6RA,51151@151>R>571571g00SFR@'A%6A,51151?=71>571/A@%V=5E=3E%U=P1P11B1<P6%T1R=C=P0P11B1;P7P=C=C=%R1%Q1R=1419R91418R@'8,2=P1P@g00T2R>%@8,419?19R8C9,2=5>=%L4R4P=1413R?%@3,415?1R3,88,2=P4P=18?9,2=P418?@,2=P1P@P>P3C9,2=5>=C;C;C;1K=5P2P6g00TYR=g00U9R5'I1M26=N=5dg00UY=H10COb@bAbBX21X31X41X51X611070117<,<0':11<;1107'0106;107<117;,<<':[[[^21^31^41^51^61P2f6f7R5f8R=P6f9P0P7P<O8b?O2W>XC1P=P5P<P7CFeW=W<W;X:1X81X91X71X1:X0:P;P<P7P6P0P2O6X:1X81X91X71X1:W0o"). Qed.
Lemma defined_dkr M M' a n : dkr M M' a n -> L5.defined M a n -> L5.defined M' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) [] "h01Mh12M'h24__x1h34__x2h44__x3h51ah61nh71Dh81Hh92H0h:2H1h;2Hih<7__arithh=4__ffh>8__varmaph?5__with@1ip;1p;4p;3p;2p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up4p710R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p4p70p1007]p4p771111110p8P1p1008bp4p710p8g009@j11Tg009ej1=Tg00:Cj19Tg00:fj1@Tg00@3j4PTg00V7j3<Tg00<Hj22Tg00=Aj20Tg00=]R1j27Tg00<dj23Tg00DWj1?Tg00EWj1>Tg00F7j2:Tg00G3j4OTg00GQj1NTg00Goj1MTg00HZj26Tg00I=j1FTg00JEj45Tg00>^j1ETg00W5j2DTg00Ibj3;Tg00NMj7CTg00K0j2BTg00KRj2GTg00Klj2HTg00?@j3ATg00LXj3ITg00M7j4JTg00Mij7KTg00O1j8LTf1R0g00P<R2g00P[R3P3g00Q;R4f0R5g00Q[FKp=4f3R6P2P3P3P4f2R7P0P5GLp=8g00A7R8#1R9#1#1R:#1#1#1#=#9%=:#9#@[R:g00A\R;P6P7P0P5CPf4R<?<70g00UYR=/251056'7P6f5R>/30P112=0100<f6R11317R?'2131>,0?'7P512=6f7,0<g00R;R?#?%>?P;1:;7P01:;6CO%N;%M;R?P;16;9R9g00T2R>%F8,6;R@C5,4?%E3RAP?P;1D;=g00OURBP9C5,4?PAP?P2P3P3P4P;16;8R8PBA;;89R9C5,4?P;P9P>A;;8@C5,4?FCC8C81B?4P5P7g00TYR?g00U9R4'G1H57=A?4dAI;=0CJb=b>b?X2;X3;X4;100712=71376R=,27137<,0='7[[^2;^3;^4;P5f9P1f:P0P7O5b<W:W9P0P5O2n2001000000120000000P7P0P5O2O3W;X@;A<<67eW8W7X6;X5;X1:X0:P6P7P0P5O4X6;W5X1:W0o"). Qed.

Section Agree.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Variable vpa : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').

Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply PMF.ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply PMF.ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply PMF.ag_sub; [exact AG|lia|lia]|lia|lia|exact H].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mstate_at_agree a s : 0 <= a -> a + 24 <= 2 ^ 64 -> ag a 24 -> PQM.mstate_at segs M a s -> PQM.mstate_at segs M' a s.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "h02T4h12T3h24__x1h37__arithh44__ffh57__sat17h67__sat18h78__varmaph85__with92Hah:1Hh;1ah<1sh=2AGh>2H0h?3H16h@2H8hA3Ha'p;1p;2p;4p;3p;9p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p606000p1007]p4p771111110p8P1p1008bp4p710p8g00I=j1]Tg009@j13Tg00WXj18Tg00<dj20Tg00X6j2XTg00<Hj22Tg00;Hj4PTg00XSj4>Tg00YVj1=Tg00ZWj4<Tg00[Tj1:Tg00\Tj1;Tg00=]R1j2@Tg00]Tj4?Tg00^Qj2WTg00=Aj2BTg00_9j3VTg00DWj1UTg00EWj1TTg00F7j2QTg00GQj1OTg00Goj1NTg00HZj2MTg00K0j2LTg00KRj2KTg00Klj2HTg00?@j3ITg00LXj3JTg00M7j4GTg00W5j26Tg00_]l9ATg00>^j1FTg009ej1ETg00`aj3RTg00aDl9STg00bNl9DTg00cRj4CTg00JEj4\Tg00Mij7[Tg00Ibj3ZTg00O1j8YTg00UYR0f0R2'2p=5f4R3f3R4f2R5f1R6'0P2C?p=4P5g00P<R7g00P[R8P8g00Q;R9g00A\R:P6g00OUP2C\g00Q[F[p=1AZ:62p=7P4P7P8P8P9P5P6P2GYp=9g00cmR7%56R;g00A7R<#]#3#3#3#8R=,05%3<R>#8R?%3>R>#3R@#3RA#3#3RB#8RC'XRD'2p,1MREp,2M'RFP4P=CPp,4segsRGPEP3P4C>P1PGPEf5R4%=3C<PGPEP4%8@R@%:3D4PGPEP4%8ARA%;3D4'@PGPFf6R3P4C>P2PGPEf7RH%=3C<PGPEf8R3P@%:HD4PGPEP3PA%;HD4'@P1PGPEf9R1P@%:3D4PGPEP1PA%;3D4PGPFf:R3P1C>P2PGPEf;RHP@%:3D4PGPEf<R3PA%;HD4PGPFf=RH%=3RIC<PGPF10H@RJ%:3RKC?RLPGPF10HARM%;3R3C?RN'@PGPEPFPHPIPEPFPHP=PH%8>R>P11W?CRI1B0?%5C1B0D[[RO%5?RPg00doRQAV?C6UW9RC%5D\Q^9PRPp,2T4PFO1RQp-0RR\:RS\:RT\:RUP2f@O1RVPTP2fAO1RWPSP2fBO1RXPRp,2T3PFO1RYPTP2fDRZO1R[PSP2fER\O1R]PRg00R;R^#UR_%T^R^1Q:6R`%O:Ra%N:Rb1M:<R<;1<1Lb9R9P2P5g00TYRcg00U9Rd'K1H25=IcddAJ:06CGRdb4b7b8X2:1222^2:P2fGRcO1R5b3b1b1b1b0b0b0b0b5b6PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`Pa16:>,7<Re16:=,7<Rf51bP9Pdb4b7b8X2:102>102=Rg'2^2:P5b3b1b1b1b0b0b0b0b5b6M9APIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`PaPb16:0R0=1b<Rh%F8R8PhC9P9Pdb4b7b8X2:%52RiP;[^2:P2PcP\O2R\b3b1b1b1b0b0b0b0b5b6PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`PaPb16:?%EB5R:RB91bfR?P8A1beBC9P9Pdb4b7b8X2:12gDRe106>/2D[^2:P2PcPZO2RZb3b1b1b1b0b0b0b0b5b6P4M9SPLPNPGPEPFPJPKPEPFPHP=PJP@P1PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`Pa16:@RJ,7<RK91b<P9Pdb4b7b8X2:102@RN,22^2:P5b3b1b1b1b0b0b0b0b5b6PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`Pa17KJRL=1bfP9Pdb4b7b8X2:10N@/2g^2:P5b3b1b1b1b0b0b0b0b5b6M9APIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`PaPbPhP8A1b0KC9P9Pdb4b7b8X2:106@RK#5\i^2:P\b3b1b1b1b0b0b0b0b5b6PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`PaPbP?P8A1bLBC9P9Pdb4b7b8X2:10K@/2D\e^2:PZb3b1b1b1b0b0b0b0b5b6P6M9DPGPEPFPMP3PEPFPHP=PMP@P1PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`Pa16:A,7<R191b<P9Pdb4b7b8X2:102AR<,22^2:P5b3b1b1b1b0b0b0b0b5b6PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`Pa171JRJ=1bfP9Pdb4b7b8X2:10<@/2g^2:P5b3b1b1b1b0b0b0b0b5b6M9APIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`PaPbPhP8A1b01C9P9Pdb4b7b8X2:106ARA#5\i^2:P\b3b1b1b1b0b0b0b0b5b6PIPOPCPPPQPUPVPTPWPSPXPRPYPTP[PSP]PRP_P^P`PaPbP?P8A1bJBC9P9Pdb4b7b8X2:10A@/2D\e^2:PZb3b1b1b1b0b0b0b0b5b6P2M9DCCCCW?W@P6P2O2n2001000000121000000W:W>P6P2O2n2001000000121000000W:W=WAW9X<7X;:P6P2O2W<X;:o"). Qed.

Lemma mvec_at_agree v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PQM.PSZ * 2 ^ k <= 2 ^ 64 -> ag v 24 -> ag b (PQM.PSZ * 2 ^ k) ->
  PQM.mvec_at segs T3 T4 M v b k stk -> PQM.mvec_at segs T3 T4 M' v b k stk.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "h02T4h12T3h24__x1h31Hh42H0h52H1h62H2h72H3h87__arithh94__ffh:7__sat17h;7__sat18h<7__sat19h=7__sat20h>7__sat21h?8__varmaph@5__withA4cstrhB1ihC1qhD1rhE2HahF4__p1hG4__x2hH4__x3hI3Hn0hJ4__x4hK5cstr0hL4__x5hM4__x6hN1bhO1khP3stkhQ1vhR3AGBhS3AGVhT2DBhU1EhV2ELhW3HalhX2HbhY3Hb'hZ2Hkh[4Hlenh\2Hnh]3Hn1h^2Hvh_3Hv'h`2Hxha2P2hb2V0hc3V16hd2V8he2_Hhf3_H0hg1np%0p%1p&0p;1p;2p;4p;8p;3p;9p;6p;7p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0g001cR0p4p710R1p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R2p1005_p4p710p8P2P1p8P2p1006Ap4p710R2p8p1006]p606000p1007]p4p771111110p8P2p1008bp4p710p8g00EWk10=Tg00I=j1pTg009@j1JTg00WXj1PTg00X6j22Tg00;Hk408Tg00eKj8ETg00]Tj4VTg00<Hj23Tg00fLR2j16Tg00flR1j2?Tg00V7j3`Tg00=]R3j21Tg00gDj1NTg00gij3bTg00hZj29Tg00^Qj2WTg00_9j3XTg00i:j2eTg00?Zk10@Tg00i[j2CTg00j8j2kTg00=AR4j2;Tg00j_j2jTg00kFj2hTg00klj2gTg00DWk10VTg00GQk10UTg00Gok10TTg00W5j2\Tg00HZk20<Tg00>^k10STg00K0k20QTg00KRk20;Tg00Klk20PTg00?@j3aTg00LXk30NTg00M7k40MTg00lRk20KTg00<dj27Tg00_]l9rTg009ek10JTg00`ak30ITg00bNm901Tg00mRj2>Tg00mok60HTg00o4j4|Tg00B:j1RTg00BYk206Tg00Ckj2oTg00E7j3nTg00FUk10GTg00JEj4mTg00o[j2uTg010Gj3^Tg010jk10FTg011Hk20ETg011ij3lTg012Rj2yTg013;j3xTg013dk60DTg014Hk60BTg00cRj4vTP0k200Tg015Xk405Tg00XSk40:Tg00F7k20ATg00Mij7tTg0164k60LTg00NMk70?Tg00O1j8cTg00Ibk30OTg016Xm<0>Tg00CBk303Tg00G3k40RTg00UYR0f0R5'3p=0f2R6f1R7'7/35p=<g017=R81275'>p=@g00cmR90005#6p=U1>85p=5f5R:f4R;f3R</761775CVp=I13061375'1p=L20095,?7p=HP:P;17<6P9P7P5g018:R=H05H0:p=8g00A\R>f7S00f6R?'9;a0A`:;<1175,16'1'1p=F1175,16p=G20095p=41367/15p=s%65,>8p=D1975=a>0p=~A`:;<1175,16'1p>071;05p=KAa>50p=O1>67/75p=QAa>75p=B1375,16p=i20A>5p=]P6g00P<S01g00P[R8P8g00Q;R@P>P7g00OURAP5Cmg00Q[RBFtp=:P7Q01P8P8P@P5J0Lp=fP6Q01P8P8P@P7P5K0?p=dP<Q01P8P8P@P6P7P5Gcp>04P9P7P5P=H05p>09P;P<1767P5H0:p>02B0O>75p=AP:Q01P8P8P@P;P<P6Q01P8P8P@P>P7PAP5CmPBFtGcp=M20;>5p=Yg019;RAP>P1P2P4g019ZP:P;P<P6P7P5N<0>p=}1307/15p=_206>5p=ZB03>75:03>6p=[P>P6P7P5H0Rp==20<>5p=TP7Q01P8P8P@P5PBFtp={P?Q01P8P8P@P:P;P<Q01P8P8P@P6P7P5GcGcp=SB03>75p=zP>P7g01:<P5Cmp=wP;Q01P8P8P@P<P6P7Q01P8P8P@P5PBFtGcp>0CP?P:P;P<P6P7P5CvCvp=q&0=9S02Q02%0<S03g00A7S04#pS05#JS06#J#J#PR9Q04#JS07#PRBQ07#JS08#JS09#JR4#J#JS0:#PR2'2R15<;%0;S0;1@B;=<:1p,1MR=p,2M'RCQ00P9H08P=PCQ001@B?H08p,4segsRDp,2T3REp,2T4RFP=f9RGf8RHQ00P?GEP3PDP=f:S0<PGCVPDP=Q0<Q09#PRIPGQ00#URJ#5RKEIPDP=Q0<%P4R4PG12BHRL#5RMEIQ07#pS0=#p#PRN9LHH13JLPGP4P=PGPMPEP=PGPKO3PFP=PGPKPMO41H5HPDP=f;RM%67S0>#5RKP7PGE8[^BAGF3G3GPDPEPFPCPMQ0<PGPHGEP5PDP=f<RLPMCVPDP=f=RJPIPLQ0<#URO#5RPEIPDP=PJP4PL12BMRQ#5RREIALMMN13OQPLP4P=PLPRPEP=PLPPO3PFP=PLPPPRO4%4MRM,?5PDP=f>S0?PKP7PLE8[^BAGF3G3GP3PDP=Q0?PIPJ%6MRM#5RREIPDP=Q0?P4PJ12BLRP#5RQEIALLLNPJP4P=PJPQPEP=PJPRO3PFP=PJPRPQO41H5LPDP=f?RQPKP7PJE8[^BAGF9sMP3GPDPEPFPCPQQ0?PJPLGEP5PDP=f@RLPIPQ%4J#DEIPDP=fARJP4PL12BQRP#5RMEIALQQNQ0?#URRPLP4P=PLPMPEP=PL%5RRRO3PFP=PLPRPMO4%4QRQ,?5PDP=fBS0@PKP7PLE8[^BAGF7sP3GP3PDP=Q0@P4PJ12BLRP#5RMEIALLLN%6QRQ/3PPJP4P=PJPMPEP=PJ%5QRQO3PFP=PJPQPMO41H5LPDP=fCRMPKP7PJE8[^BAGF3GPDPEPFPCPMQ0@PJPLGEP5PDP=fDRLP4PMQ0@,@BEIALMMNQ0@#URJ12BMRQ'3PLP4P=PL%5QRQPEP=PL%5JRJO3PFP=PLPJPQO4%4MRM,?5PDP=fFS0APKP7PLE8[^BAGF3GP3ALLLN%6MRM12BLRQfES0BP4P=Q0B%5QRQPEP=Q0B%5MRMO3PFP=Q0BPMPQO41H5LPDP=fGS0CPKP7Q0BE8[^BAGF3sPDPEPFPCQ0CQ0AQ0BPLGEP5Q0AQ0A;LNQ0A#URLQ0C,2BRQfHRMP4P=PM%5QRQPEP=PM%5LRLO3PFP=PMPLPQO4Q0C#4RQ,?5PDP=fJS0DPKP7PME8[^BAGF3sP3%6QRQ12BMRL'3fIS0EP4P=Q0E%5LRLPEP=Q0E%5QRQO3PFP=Q0EPQPLO41H5MPDP=fKS0FPKP7Q0EE8[^BAGFPDPEPFPCQ0FQ0DQ0EPMGEP5Q0E#UQ0D,2B'3fLRMP4P=PMQ0F,@BRLPEP=PMQ0D#4#DRQO3PFP=PMPQPLO4Q0F#4RL,?5PDP=fNS0GPKP7PME8[^BAGFP3fMRQ/~4P=PQ1@BMRJPEP=PQ%DLRLO3PFP=PQPLPJO41H5MPDP=fORJPKP7PQE8[^BAJ07PDPEPFPCPJQ0GPQPMGEP51~J4P=fPRM1@BJRQPEP=PMQ0G#4#DRLO3PFP=PMPLPQO4%4JRJ,?5PDP=fRS0HPKP7PME8[^BAJ07P3fQRQ1@BMRL5`=PEP=PQ%DJRJO3PFP=PQPJPLO41H5MPDP=fSRLPKP7PQE8[^BA3GPDPEPFPCPLQ0HPQPMGEP5Q0H,@B9`=LPEP=fTRMQ0H#4#DRQO3PFP=PMPQ1@BLO4%4LRL,?5PDP=fVS0IPKP7PME8[^BA3GP3PEP=fURQ%DLRLO3PFP=PQPL1@BMO41H5MPDP=fWS0JPKP7PQE8[^BA'1PDPEPFPCQ0JQ0IPQPMGEP5PEP=Q0J%4Q#DO3PFP=fXRQQ0I#4#DQ0J,@BO4Q0J#4RM,?5PDP=fZS0KPKP7PQE8[^BA'1P3PFP=fYR3%DM1@BQO41H5QPDP=f[S0LPKP7P3E8[^BAPDPEPFPCQ0LQ0KP3PQGEP5PFP=Q0L%43#DQ0K,@BO4Q0L#4RQ,?5PDP=f^RMPKP7f\S0ME8[^BAQ0M%NQ%6Q#0AbM43%04S0Nf_R3/94#0[1WB2RQ%KBS0O%02%K1[[RL%0BRJg00doRPAXB27UWER2%01\P^EJRRf`S0P,WBQ0OfaS0Q#0fbS0R,2BS0S#K[[fcS0T=XB7VPXEJQ0T,2BRO#0\P^EJQ0T/e4%O4RS$0@S0UfdRT1CT419T45Q4'B[1kT4%K4S0VfeS0W/94RU#0S0X1;U4'1[Q0W/j41;40S0YffS0Z/94RV,;4?iV0[Q0Z/h4fgS0[/C4#O\SQ0[/g4fhRW/94/BW\S1CW4RXP>fiRY/94RZP>PFPCO1R[p-0R\\>R]\>R^\>R_P5P6O1R`P^P5P<O1RaP]P5P;O1RbP\PEPCO1RcP^P5P?O1RdP]P5Q00O1ReP\g00R;S0\$0VRfQ0\$0=Rg%]7Rh&0U>Ri&0T>Rj1\>0S0]Q04-0<>Rk5:jS0^1fj<5dj&0S8RlQ0^H0420Qj@RmP5P6g00TYRng00U9Ro+0;20P56=anodB0N>07H0MRob9b?b@X2>XF\%05S0_/17%07S0`[^2>^F\P5fqS0a/3NQ0aQ0KO3b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bA+0KQ0M,2B#KPDPCP3PMCVPDPC173IS0bQ0M#4Rn#6Rp#5Rq,7MS0cCVS0dPDPC1734S0ef]S0f,2BS0g#5Rr,7MS0hCVS0iQ0fQ0f;LNS0jQ0g,3pS0k1~M4S0lA`CMrS0mPEPCPMPqO3S0nPFPCPMPqPrO4S0oQ0f,H5S0pPDPCQ0PPK2097MS0qI02[^BAS0r'1S0s'1S0t'1S0u'1S0v'1S0w'1S0x'1S0y'1PDP=PCP3PMP=PCP3P9P3PIQ0J%NnRn%0pRpQ0K9b34RKQ0NQ0P/94#0[RrPQPLP2PRQ0Q,WBRqQ0OQ0R#0%KO[[ROAXBT7VPXEJRs12BT#0\P^EJRt1eT4RuQ0UQ0WQ0W/C4=Q4U'B[RUQ0W/k4RvQ0V%0VS0z1;V4'1[RVQ0Z/j4RwQ0YQ0[/94S0{,;4Q0{;i0[RxQ0[/h4Ry%OX\SRX1gW4Rz1BZY\SRZ1CY4R{P>fjR|/94R}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiA:jkkPmPob9b?b@X2>1355^2>P5ftS0|O1S0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPi1\>IS0~,AkS101\>9R~,AkS115:jPmPob9b?b@X2>175IS121759S13'3^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAM9rPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiPjQ0^PlQ0^H04PmPob9b?b@X2>Q0_Q0`[^2>P5Q0|fpS14O2S15b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiPjQ111\>BQ0:$0J60I>S0:5:jS16PlPjQ10Q0:EMPmPob9b?b@X2>Q13/31S17177IS18/31[^2>P5Q0|foS19O2S1:b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0HN901Q0dQ0yPDP=PCQ0bQ0cP=PCP3P9Q0bPIQ0JPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiQ109:jkPmPob9b?b@X2>Q12,35^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiQ10Q0~'AS0bQ115:jPmPob9b?b@X2>Q12Q137<I^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAM9rPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiPjQ0^PlPjQ0]Q10EMPmPob9b?b@X2>Q0_Q18#0[^2>Q15b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiPjQ16PlPjQ0bQ0:EMPmPob9b?b@X2>Q17Q18?<I1[^2>Q1:b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0GN901Q0iQ0xPDP=PCQ0eQ0hP=PCP3P9Q0ePIQ0JPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPi1\>4S0J,AkS0e9:jkPmPob9b?b@X2>1754S0h,35^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiQ0eQ0~'AS0~Q115:jPmPob9b?b@X2>Q0hQ137<I^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAM9rPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiPjQ0^PlPjQ0]Q0eEMPmPob9b?b@X2>Q0_1774S0e#0[^2>Q15b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAPnPpPKPrPQPLP2PRPqPOPsPtPuPUPvPVPwPxPyPXPzPZP{P>P}P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgPhPiPjQ16PlPjQ0~Q0:EMPmPob9b?b@X2>Q17Q0e?<I1[^2>Q1:b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0DN901Q0jQ0wQ0AQ0kQ0vQ0@Q0lQ0uQ0?Q0mQ0tP=PCPMQ0g,>9Q0IQ0<J0HQ0nQ0sg01:cRhQ0oQ0rPhQ0pP<P7P5O2PDP=Q0PQ0>,>9Q0qI02%43Rh,?6%66R{%6hRZ';RzP6P{%Y{PhPZ%YZE}P7C|Pz%N<%6<Rz#0Q0Q#4RZ#N%6ZRh#0AbT43Q0NQ0X[PQPLP2PRQ0Z,WBQ0OQ0[#012BW#K[[AXBY7VPXEJ12BYS0X#0\P^EJ1eY4Q0U1C|4=Q4},B|[1k|4Q0VfkR}/94RT1;T4'_[1j}4Q0YflRX/94Ry,;4?iy0[1hX4fmRx/C4#O\S1gx4fnRw/94RV/Bw\S1Cw4RvP>Q19/94S0qP>P[P_P`P^PaP]PbP\PcP^PdP]PeP\Q0\g00RgRU#R#RRu#RS0>#ZRt%ZuS0r206>URU3[g00SFRu'o;nfPg&0G>Rs%];RO7=6%]<Rq?=;s7=7PiPjP>Pkg00T2Q06#TRrCm,{jPlPjQ07#TRK9:jrPlPjQ0]Q0=#T5:jRr1fj?5djPlQ04#PRp,\>,Ak=:jKS0=H04FSPmPob9b?b@X2>XG>XH>XJ>XF\1;5<13;6Q0;/1?A<<p;[[[^2>^G>^H>^J>^F\P5fwRn/3Nfv#UPn12BnQ0E#6Q0AQ0MQ0PO8b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIQ0P,2B9<{pQ0P#4R{,?<%6{Rn,;zS0AP<Pz%YzP{Pn%YnE}P6C|Q0A%N;%6;Rn#0Q0R#4R{#N%6{#0Q0WQ0P7b4Q0NQ0z[PQPLP2PRQ0[,WBQ0O%0WQ0X#K[[AXB|7VPXEJ12B|S0X#0\P^EJ1e|4Q0U1C}4=Q4T,B}[1k}4Q0V1;y4,_y[1jX4Q0Y19x4RT,;4?iT0[1hx4%Ov\S1gw4Q0qQ19'B\SQ19/C4S0qP>Q14/94S0[P>P[P_P`P^PaP]PbP\PcP^PdP]PeP\Q0\1zUt/ou,uU;nfS0zPg%]6S0WA=q<s7=7S0PPiPjQ0=PlPj1fj:9djrS0=PlA^>~k/A~A^>~KRv5:jFSPmPob9b?b@X2>XG>XH>XF\A<5p7Q03/1;S031>96Rp1>9<R|7<9S0A[[^2>^G>^H>^F\P5fxR{/3NP{12B{Q0D#6Q0CQ0QO6b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbI1>9zQ0Q,2B,>97<9Q0T1>9n'7S0DQ0Q-09;S0E1?;Z1;nhRzP;Pn%YnPZPh%YhE}P<C|S07Pz%N:S06%6:#0S0oQ0T#4Rh#NS0s%6h#0S0nQ0ZQ0Q7b4S0ZQ0NQ0{#0[S0NPQPLP2PR1WBWS0{Q0O%0YQ0X#K[[S0OAXB}7VPXEJS0X12B}#0\P^EJRJ1e}4R}Q0U1CX4=Q4y,BX[Ry1kX4RXQ0V1;T4,_T[RT1jx4RxQ0Y1;4V?iV0[RV1hw4RwQ0q#O\SR0Q19/g4RPQ0[Q14'B\SRYQ14/C4RWP>Q0a/94RhP>P[P_P`P^PaP]PbP\PcP^PdP]PeP\Q0\Q04$0F-0E>RZQ0>#RS0>#RS04#ZR{5l>Al>Zt;[UQ05#P,y>=x>{,zU1y>4=x>UQ04#RS04#R#Z1z{t3[/ou'u'u;nfPg%]:S0a?=:s?=6sA=q:O7=7PiPjPjPjQ01P8P8P@Q0JQ0]'w,{jJ0DPlPjQ0JQ09#T5^>Q05#p#TR@'A,wkI0CS0JPlPjQ0]=:jKS09PlPjQ0],w@,{jS01PlPjQ00,fj9djrPlPjQ0^PlPjQ0]1AkvR@EMFSFSPmPob9b?b@X2>XG>XH>XJ>XL>XF\g01;?\SS0]AQ4:;,B7[%06%O:1_:HQ0;1>9?RS,7:S0^#0[[[[[^2>^G>^H>^J>^L>^F\P5fyRK/3NS0;PGPHPKQ0F#6RNfzR8Q0?Q0BQ0KQ0RfuO;b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIQ07PzQ06Q0oQ0sQ0nQ0ZQ0NPQPLP2PRQ0{Q0OQ0XPJP}PyPXPTPxPVPwP0PPPYPWP>PhP>P[P_P`P^PaP]PbP\PcP^PdP]PeP\Q0\A[{tU1y>I=x>UQ04#Z9l>ZQ0>#Z9l>ZQ0r5[{3[/ou'u;nfPg%]??=<s?=6sQ0a9=O?7=7PiPjQ0JPlPj1Av~RvQ08#T9^>~RO5:jPlPjQ01PlPj1fjH9djrPlPj1AkOQ0:5:jPlPj1A@~ROQ0:EMFSFSPmPob9b?b@X2>XG>XH>XJ>XL>XM>XF\Q0]AQ4?:,B7[Q0A%O?1_?GA<;S1Q0^?<91[[[[[^2>^G>^H>^J>^L>^M>^F\P5Q0;PGPHPK12BKRBPNP8Q0?Q0CQ0KQ0RQ0|O<b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIP=PCQ0TQ0S,>9Q0DP9Q0LQ07PzQ06Q0oQ0sQ0nQ0ZQ0NPQPLP2PRQ0{Q0OQ0XPJP}PyPXPTPxPVPwP0PPPYPWP>PhP>P[P_P`P^PaP]PbP\PcP^PdP]PeP\Q0zPgQ0PPiPjQ09PlPjQ0=PlA:jk@FSPmPob9b?b@X2>XG>XH>XF\Q0`Q03176|,36[[^2>^G>^H>^F\P5Q0;PKPNP8Q0BQ0RO6b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIQ07PzQ06Q0oQ0sQ0nQ0ZQ0NPQPLP2PRQ0{Q0OQ0XPJP}PyPXPTPxPVPwP0PPPYPWP>PhP>P[P_P`P^PaP]PbP\PcP^PdP]PeP\PfPgQ0W?=7qPiPjQ05#T9^>~R~9:jvPlPjPO1Ak~EMPmPob9b?b@X2>XG>XH>1>97?<9p177p177|7<9[^2>^G>^H>P5PBPNP8Q0CO4b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIM9rP6J0BPDPCQ0T%5nQ0EI02eb`b]bUW\XgACvFqFqFqFqPDPEPFPCP3PMQ0fQ0MGEebaWVWfP7P5O2n2001000000121000000W3WeP7P5O2n2001000000121000000W3WTP7P5O2n2001000000121000000W3WWP7P5O2n2001000000121000000W3W[P7P5O2n2001000000121000000W3WZP7P5O2n2001000000121000000W3WcP7P5O2n2001000000121000000W3WdP7P5O2n2001000000121000000W3WbP7P5O2n2001000000121000000W3WRWSWYWXW_W^WPXO>XN>XQ>P<P6P7P5O4WPXO>XN>XQ>o"). Qed.

(* [comment removed for export] *)
Lemma v8_at_keep v x : 0 <= v -> v + 24 <= 2 ^ 64 -> ag v 24 ->
  (forall b n c, x = PQV8.V8Blk b n c -> dkr M M' b c) ->
  PQV8.v8_at segs T3 T4 M v x -> PQV8.v8_at segs T3 T4 M' v x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "p'0h02T4h12T3h21Hh37__arithh47__sat17h57__sat18h64__x1h72H0h82H1h92H2h:2H3h;4__ffh<7__sat19h=7__sat20h>7__sat21h?7__sat22h@7__sat23hA8__varmaphB5__withC1qhD1rhE2HahF1bi001bhG1ci011chH1ni021nhI2DKhJ2W0hK3W16hL2W8hM2_HhN1vi031vhO1xi041xhP2AGhQ1DhR2DBhS3HalhT2HbhU2HchV2HnhW2HvhX3Hv'hY3_H0p%0p;1p;2p;4p;3p;6p;9p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p606000p1007]p4p771111110p8P1p1008bp4p710p8g00I=j1JTg009@j1HTg00WXj1=Tg00<dj20Tg00X6j2TTg00<Hj22Tg00;Hj4jTg01;\j3STg00?@j3<Tg00@3j4dTg01<Wj6RTg00V7j3ATg00=]R1j21Tg00moj6iTg00^Qj2VTg00=Aj2?Tg00_9j3UTg00DWj1hTg00EWj1gTg00F7j2fTg00GQj1eTg00Goj1cTg00HZj2bTg00K0j2aTg00KRj2YTg00Klj2`Tg00LXj3{Tg00M7j4zTg00W5j2GTg00Ibj3ITg00_]l9DTg00>^j1yTg009ej1xTg00`aj3wTg00bNl9ETg00]Tj48Tg00gij2sTg00hZj2>Tg00i:j2rTg00?Zj1qTg00i[j2WTg00mRj2pTg00j8j2oTg00j_j2nTg00kFj2mTg00klj2lTg01=Sj6tTg00cRj4XTg00JEj4kTg00Mij7uTg00O1j8vTg00UYR0f0R2'2p=:%H2#Hp=Bf3R3f2R4f1R5/02P0C8p=Qf6R6f5R7f4R8P0C8P3P4P5P0C8/12'1p=@1252,14p=^1245/12p=Pg00A\R91>52;<0p=OAA8341152'1p=41152,14p=NP8P3P4P5C8/12p=3P4P5P2P0C8p=9P7P81034P5C8/12p=_P3P4P5P0C8/12p=ZP4g00P<R:g00P[R;P;g00Q;R<P9P5g00OUP2Ckg00Q[Fup=;P3P:P;P;P<P4P5P2Gvp=FP6P7P8P3P4P5P2CXCXp=C12831>45=<90/12'1p=6f7R:,201267'112831245'1/12'1p=7P7P8P31045C8/12p=KP6P710831045C8/12p=5P8P31045P2C8p=L1205/12p=M12831245'1/12p=]1>45=<90/12p=\A<920p=[g01>_R=%:5S00g00A7R>#JR?#HR@#B#=RA,04%H>RB#=RC%BBRB#HRD#BS01#=RE'TRF'2p,1MRGp,2M'RHP3PACjAS452RI9<=6PGPHP3P5CdS02[^G9^H9^F9p,4segsRJp,2T3RKp,2T4RLPGP7P8ERP1AAG6APKPGP6PAO3P=p-0RMP7PJPGP6PJPG%=BRB,06PJPGP6%=DRDCQF@PJPGf9RNP4PJPG10NBRO1045RPPJPG10NDRQ1042RRQ00?^52RS%=>RT%J@#J#=S03,TCS04%J?#J#=R?,TCS05'0R@,227P2RUQ01#B#B#B#=RV/24RW1O4DRXPGP4P2PKPGP4P5O3PLPGP4P5P2O4D43N3NRYD3D3D3n0110400020030100102101'1PJPKPLPHP:P6ERP2f8RZ=AGAPKPGPNPAO3P=PMPZPJPGPNPJPGPOA9JGQF@PJPGf<RQP4PJPGPQPBPPPJPGPQPDPRPYE_E_D3n0110400020030100102101'1P1PKPGf:ROPAO3P=PMPNPJPGPOPJPG10OBPJPGPOPDCQF@PJPGf=R[P4PJPG10[BR\PPPJPG10[DR]PRPYD3D3D3n0110400020030100102101PJPKPLPHf;R^POERP2PKPGPQPAO3P=PMPQPJPGP[PJPGP\A9JG]F@PJPGf@R]P4PJPG10]BR\PPPJPG10]DR_PRPYD3D3D3n0110400020030100102101f>R`=AHAPKPHP`PAO3RaP=PMP[PJPHP`PJPH10`BPJPHP`PDCQF@PJPHfARbP4PJPH10bBRcPPPJPH10bDRdPRPHP4P2PKPHP4P5O3PLPHP4P5P2O4D49NWX9NSURUD3D3D3n0110400020030100102101RS'1PGPHP`PAPOP7EiPaPSg01:cS06P=A<=3IQ02[^G9^H9^F9P=PMP5A9JG]RSPJPGP\A9JG_CZR_'1PJPGfCR\P4PJPG10\BRaPPPJPG10\DRXPRPYD3D3D3n0110400020030100102101P=PMP4PJPHPbPJPHPcA9JHdF@RdPJPHfDRcP4PJPH10cBRYPPPJPH10cDRPPRPUD3D3D3n0110400020030100102101]2]IP[g01?Z=<=IQ02[^G9^H9^F9PJPGf?RUPJPG10UBPJPGPUPDCQF@P1PSP_PdP2fBRd99JGPJPGPaA9JGXCZP1A9JGYA9JGPPJPHfERPPJPH10PBS0710PDS0899JHF@P2fFRY/0BS0999JGfGRX/0DS0:99JGfHRa99JH10aBS0;99JHS0<10aDS0=99JHS0>'1PJPGPHPaP0PGPHPaPAPaPBPc1VCER_1?0CS0?%:E1?0F[[RS%:CRRg00doRWAUCE5UWERE%:F\W^ERRePLPHO1RfPM\9Rg\9Rh\9RiP2fKRjO1RkPhP2fLRlO1RmPgP2fMRnO1RoPMPKPHO1RpPhP2fORqO1RrPgP2fPRsO1RtPMg00R;Ru#hRv%guRu1f95Rw%e9Rx%c9Ry1b9>R>;;>1ay<R<P2P4g00TYRzg00U9R{'Y1`24=<z{dA{905CzR{b;bAbBX69S0@1222^69S0AP2fRRzO1S0Bb3b1b1b1b0b0b0b0b4b5P_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPx1G9BS0C9I9>R|1G9A9I9>R}5;yP<P{b;bAbBX69S0D102BS0E102AR~'2^69S0FQ0Bb3b1b1b1b0b0b0b0b4b5M9DP_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxPy1G90S0G=;y>S0H%y;S0IQ0HCFP<P{b;bAbBX69S0J%:2S0KQ00[^69S00P2PzPsO2S0Lb3b1b1b1b0b0b0b0b4b5P_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxPy1G9CQ01#x5w9R;9;y}S01Q0IA;y|;CFP<P{b;bAbBX69S0M12~FS0N105BS0O/2F[^69S0PP2PzPqO2S0Qb3b1b1b1b0b0b0b0b4b5P7M9EQ0<Q0>PJPGPHQ0;P0PGPHPaPAQ0;PBPcP_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxA;y>|P<P{b;bAbBX69S0;Q0E,22^69S0>Q0Bb3b1b1b1b0b0b0b0b4b5P_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxQ0C9I9|S0<=;y}P<P{b;bAbBX69S0RQ0E/0B/2~^69S0EQ0Bb3b1b1b1b0b0b0b0b4b5M9DP_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxPyQ0HQ0IQ0G=;y|CFP<P{b;bAbBX69S0SQ0KQ0O#:[^69S0TQ0Lb3b1b1b1b0b0b0b0b4b5P_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxPyQ01Q0IQ0<=;y;CFP<P{b;bAbBX69S0<Q0NQ0O/0B/2F[^69S0OQ0Qb3b1b1b1b0b0b0b0b4b5P5M9EPJPGPHQ0=P0PGPHPaPAQ0=PBPcP_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPx1G9D9I9>R|9;y>P<P{b;bAbBX69S0=102DR>,22^69S0UQ0Bb3b1b1b1b0b0b0b0b4b5P_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxQ0C9I9|S0C=;y}P<P{b;bAbBX69S0V10>B/2~^69S0WQ0Bb3b1b1b1b0b0b0b0b4b5M9DP_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxPyQ0HQ0IQ0G=;y|CFP<P{b;bAbBX69S0GQ0K105DR|#:[^69S0KQ0Lb3b1b1b1b0b0b0b0b4b5P_PSPEPePfPiPkPhPmPgPoPMPpPhPrPgPtPMPvPuPwPxPyQ01Q0IQ0C=;y;CFP<P{b;bAbBX69S0CQ0N10|B/2F[^69S0NQ0Qb3b1b1b1b0b0b0b0b4b5P2M9EFCWKWLP5P2O2n2001000000121000000W2WJP5P2O2n2001000000121000000W2WIAS783=<=IQ02[^G9^H9^F9PJPGPPP3PJPGQ07P3P4PJPGQ08P3P5P4P4P5PTP5P5P@PVP3P3PDPGP3P5PKPGP3P4O3PLPGP3P4P5O4D4D6G7EKEKD3P1PJPGPYP8C8PJPGQ09P8P3PJPGPYPDP8P4P3P3P4PTP4P4P@PVP8P8PDPGP8P4PKPGP8P3O3PLPGP8P3P4O4D4D6G7F5EKPJPHPXP7PJPHPXPBP7P8PJPHQ0:P7P3P8P8P3PTP3P3P@PVP7P7PDPHP7P3PKPHP7P8O3PLPHP7P8P3O4D4D6G7EKF5D3P2PJPGPaP6C8PJPGfIRIPBP:P6PJPGPIPDP:P7P6P6P7PTP7P7P@PVP:P:PDPGP:P7PKPGP:P6O3PLPGP:P6P7O4D4D6G7F5F5P1PJPGfJRFPB10Z:DLPJPGPFPDPZP6P:P:P6PTP6P6P@PVPZPZPDPGPZP6PKPGPZP:O3PLPGPZP:P6O4D4D6G7F5PJPHPjPNPJPHPjPBPNPZPJPHPjPDPNP:PZPZP:PTP:P:P@PVPNPNPDPHPNP:PKPHPNPZO3PLPHPNPZP:O4D4D6G7F5F5D3P2PJPGPlPB10ONDLPJPGPnPDP^PNPOPOPNPTPNPNP@PVP^P^PDPGP^PNPKPGP^POO3PLPGP^POPNO4D4D6G7F5P1PJPGfNRZPD10QODLP^P^POPTPOPOP@PVPQPQPDPGPQPOPKPGPQP^O3PLPGPQP^POO4D4D6G7PJPHPqP[PJPHPqPBP[PQPJPHPqPDP[P^PQPQP^PTP^P^P@PVP[P[PDPHP[P^PKPHP[PQO3PLPHP[PQP^O4D4D6G7F5F5D3P2PJPGPsPD10`QDLP`P`P[PTP[P[P@PVPUPUPDPGPUP[PKPGPUP`O3PLPGPUP`P[O4D4D6G7P112U`,MUPTP`P`P@PVP]P]PDPGP]P`PKPGP]PUO3PLPGP]PUP`O4D4D6D]PJPHfSR`PbPJPHP`PBPbP]PJPHP`PDPbPUP]P]PUPTPUPUP@PVPbPbPDPHPbPUPKPHPbP]O3PLPHPbP]PUO4D4D6G7F5F5D3P212b],MbPTPbPbP@PVP\P\PDPGP\PbPKPGP\PdO3PLPGP\PdPbO4D4D6D]P112d@9PTdPVPcPcPDPGPcPdPKPGPcP\O3PLPGPcP\PdO4D4D6PJPHfWRdPPPJPHPdPBPPPcPJPHPdPDPPP\PcPcP\PTP\P\P@PVPPPPPDPHPPP\PKPHPPPcO3PLPHPPPcP\O4D4D6G7F5F5D3P212c@9PTcPVPXPXPDPGPXPPPKPGPXPYO3PLPGPXPYPPO4D4D6P112VaPGPaPYPKPGPaPXO3PLPGPaPXPYO4D49\aDPJPHf[RYPIPJPHPYPBPIPaPJPHPYPDPIPXPaPaPXPTPXPXP@PVPIPIPDPHPIPXPKPHPIPaO3PLPHPIPaPXO4D4D6G7F5F5D3P212VFPGPjPIPKPGPjPFO3PLPGPjPFPIO4D49\jDP11OlDPGPlPFPKPGPlPjO3PLPGPlPjPFO4D4PJPHf_RFPnPJPHPFPBPnPlPJPHPFPDPnPjPlPlPjPTPjPjP@PVPnPnPDPHPnPjPKPHPnPlO3PLPHPnPlPjO4D4D6G7F5F5D3P21OZDPGPqPnPKPGPqPZO3PLPGPqPZPnO4D4P1AAGsZPKPGPsPqO3PLPGPsPqPZO4'1PJPHfcRZfQRjPJPHPZPBPjPsPJPHPZPDPjPqPsPsPqPTPqPqP@PVPjPjPDPHPjPqPKPHPjPsO3PLPHPjPsPqO4D4D6G7F5F5D3P2AAGzsPKPGP`PzO3PLPGP`PzPjO4'1P1PKPGfTR1P`O3PLPGP1P`PzO4PJPHfgRzfURsPJPHPzPBPsP1PJPHPzPDPsP`P1P1P`PTP`P`P@PVPsPsPDPHPsP`PKPHPsP1O3PLPHPsP1P`O4D4D6G7F5F5D3P2PKPGfVR`PsO3PLPGPdP`PsO4PJPHfjR1fXRzC8PJPH101BRq10zdRlC8RXPJPH101DRa10z`RYC8Rc12d`,MdS0:12`@9PT`S0912VzS081OzDRVAAHz`RTPKPHPzPdO3S07PLPHPzPdP`O4S02'1RL'1RK'1R@'1R\'1R]'1RU'1RQ'1PJPGPHP1PzPGPHP1PAP1PBffR^1szDRO%:z%:DfZ/>D#:[[R|1VC?R{Q0?%:?Q05,?0[[R<AUC?5VWXERR?Q05#:\W^ERR;P_PSPEPeQ03,VCRyQ0?Q03#:Q04,?0[[RxQ03=UC5VWXERRCQ04#:\W^ERRR1rFDRF%[DRW#qf`Rw1WwD,pD1>wD'05<9[Ru1owDRw1?0DfaRv/>DRt1?tD'M[Rt1nvDRv1?D0fbRr/>DRo,?D?^o0[Ro1mrDRr1WZD#[\WR01lZDRZfdRm/>D=<9m\WRW1WmDRmP9fe/>DRDP9PfPiP2P4O1RkPhP2P3O1R3PgP2P8O1R8PMPpPhP2P6O1R6PgP2P:O1R:PMQ0@Q0AP2p+01AR~O1R>b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0DQ0FP>b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@M9DPOP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0JQ00P2P~f~O2R}b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0MQ0PP2P~f}O2R~b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@PjM9EPXPQPJPGPHPqPlPGPHP1PAPqPBP^POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0;Q0>P>b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0RQ0EP>b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@M9DPOP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0SQ0TP}b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0<Q0OP~b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@PnM9EPcPUPJPGPHPaPYPGPHP1PAPaPBP^POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0=Q0UP>b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0VQ0WP>b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@M9DPOP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0GQ0KP}b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@POP|P{P<P?P;P_PSPEPePyPxPCPRPFPuPwPtPvPoPrP0PZPWPmP9PDP9PfPiPkPhP3PgP8PMPpPhP6PgP:PMQ0CQ0NP~b3b1b1b1b0b0b0b0bDbCb:b9b8b7b2b4b5b<b=b>b?b@PIM9EQ0:P]PPQ09P\PbQ08P@P[PVPKPNPTPLPGPHPzP`PsPzPdP`ASzd`,Y=O4P7EtQ07Q02Q06Q06CXFCFCFCFCWYWMP5P2O2n2001000000121000000W2WRP5P2O2n2001000000121000000W2WSP5P2O2n2001000000121000000W2WTP5P2O2n2001000000121000000W2WUP5P2O2n2001000000121000000W2WVP5P2O2n2001000000121000000W2WKP5P2O2n2001000000121000000W2WLP5P2O2n2001000000121000000W2WJP5P2O2n2001000000121000000W2WIXG9XH9XF9P4P5P2O3n0110301020131100102101PNP2O2FCW2WMP5P2O2n2001000000121000000W7WQP5P2O2n2001000000121000000W7WIWPWXWWXO=XN9P5P2O2WOXN9o"). Qed.

(* [comment removed for export] *)
Definition vs_cells (o : Z) (x : PM.vstr) : Z * Z := match x with PM.VShort _ => (o, 1) | PM.VLong _ _ _ => (o, 24) end.
Lemma vstr_at_keep o x : 0 <= o -> o + 24 <= 2 ^ 64 -> ag (fst (vs_cells o x)) (snd (vs_cells o x)) -> dkr M M' o 24 ->
  (forall c n p, x = PM.VLong c n p -> dkr M M' p c) ->
  PM.vstr_at segs T3 M o x -> PM.vstr_at segs T3 M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "p'0h02T4h12T3h24__x1h31Hh47__arithh52H0h64__ffh78__varmaph85__with92H1h:2H2h;2H3h<2H4h=2H5h>7__sat17h?7__sat18h@7__sat19hA7__sat20hB7__sat21hC1qhD1rhE1ni001nhF1ci011chG1pi021phH2AGhI3DKBhJ2HahK6__sat5hL6__sat6hM2HnhN2_HhO1ohP1xhQ2B0hR1DhS2DBhT2DKhU2HchV2HehW2HohX3Ho'hY2W0hZ3W16h[2W8i033cnti041si051vp%0p&0p;1p;2p;4p;3p;5p;6p;9p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0g001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R2p1005_p4p710p8P2P0p8P2p1006Ap4p710R2p8p1006]p606000p1007]p4p771111110p8P2p1008bp4p710p8g00I=j1JTg009@j19Tg00WXj1=Tg00<dj23Tg00X6j2aTg00<Hj20Tg01@Uj2RTg00;Hj4KTg00@3j4ZTg01A^j3VTg00?@j3<Tg01B\j5YTg00V7j3;Tg00mRj2BTg00=]R2j21Tg01=Sj6cTg01C[j1bTg01DYj4FTg00^Qj2\Tg00=Aj24Tg00_9j3[Tg00DWj1jTg00EWj1iTg00F7j2hTg00GQj1gTg00Goj1fTg00HZj2eTg00K0k203Tg00KRj2dTg00Klk202Tg00LXk301Tg00M7k400Tg00W5j2HTg00_]l9UTg00>^j1|Tg009ej1{Tg00`aj3zTg01EUl9yTg00cRj4:Tg00]Tj4>Tg00gij2uTg00hZj2CTg00i:j2tTg00?Zj1sTg00i[j2WTg00j8j2rTg00j_j2qTg00kFj2wTg00klj2xTg00bNl9XTP1j3pTg01FXj3oTg00JEj4nTg00Mij7}Tg00Ibj3~Tg00O1j8mTg00UYR1f0R0'0p=5g00A\R3?p30p=TAo330p=Mf2R4f1R5/00'1p=If4R6f3R7P4P5P0CF'1p=A1450,14p=v1045/10p=L1C50=<31p=O1150,14p=Pf5R8P61374P5C>/10p=2P6P7P4P5C>/10p=E1014/15/10p=l1045,17/10p=kP4g00P<R9g00P[R:P:g00Q;R;P3P5g00OUP0Cng00Q[F}p=8A~350p=GP7P9P:P:P;P4P5P0Gmp=D1C86=<31A;745/10'1p=610671045'1/10p=71445,17/10p=SP8P6P71345C>/10p=@P6P7P41350C>p=`P6P71345P0C>p=Qf7R9f6R<1386P7C>1014/15/10'1p=?10171445'1/10p=_1015/10p=NA;745/10p=^A<301p=]g01G5R=%55R>g00A7R?#J#9R@#9#9#=RA,34%9?RB#=RC%9B#9RD#9RE#9#9RF#=RG'aRH'0p,1MRIp,2M'RJ1R74RK#T%MKCKPIPJP6PACZAV450RK9<=9PIPJP5P7CZRL[^G3^E3^F3p,4segsRMp,2T3RNPIP<P8DYP2A;I9APNPIP9PAO3P=p-0ROP<%50S00%JB#J#9#=RB7I0RPPMPIf8RQ1BC0RRDAPMPIf:RS%=?RT,34RUPMPIPS%=DRDP5PMPIPS%=EREP0Av>54RV%J@R@#9#=RW%J@#=R@,aCRX,047L4RY1O4CRZA;I04PNPIP0P4O33P3PR[E2E2DEn0110400021010030101100102'1PMPNPJPQP9DYP0f9R\=;IAPNPIPSPAO3P=POP\PPPMPIf;R]PRDAPMPIf=R^PUPMPIP^PDP5PMPIP^PEP0P[E2E2DEn0110400021010030101100102'1P2PNPIP]PAO3P=POPSPPPMPIf<R_PRDAPMPIf>R`PUPMPIP`PDP5PMPIP`PEP0P[E2E2DEn0110400021010030101100102PMPNPJP_P]DYP0PNPIP^PAO3P=POP^PPPMPIf?RaPRDAPMPIfARbPUPMPIPbPDP5PMPIPbPEP0P[E2E2DEn0110400021010030101100102A;JaAPNPJPaPAO3RcP=POP`PPPMPJf@RdPRDAPMPJfBRePUPMPJPePDP5PMPJPePEP0A;J04PNPJP0P4O35PZ9PVYRYE2E2DEn0110400021010030101100102RV'1PIPJPaPAPSP8EcPcPVg01:cS01P=PIPJ1Rd0RV#T%MVCKA<=6KPL[^G3^E3^F3P=POP4PPPMPIfCRVPRDAPMPIfERcPUPMPIPcPDP5PMPIPcPEP0P[E2E2DEn0110400021010030101100102P=POP7PPPMPJfDRPPRDAPMPJfFRRPUPMPJPRPDP5PMPJPRPEP0PYE2E2DEn0110400021010030101100102]3]I]HP`PIPJ%b0,RbRY#T%MYCK%b6=<=KPL[^G3^E3^F3104BPMPIPV1BC4CF5l4P2%57RY?I7BPMPIPP1BC7CF%56RUP6PBPMPJPc1BC6CFCkP0%58S02?I8BPMPIfGR[1BC<CF%59S03?I9BPMPJfHRB1BC9RZCFP5PMPIPJPBPZPIPJPBPTPBPTP<1\CGRZ141CRf%5G141H[[Rg%5CRhg00doRiA[CG5UWJRG%5H\i^JhRjp,2T4PJO1RkPO\3Rl\3Rm\3RnP0PSO1RoPmP0P]O1RpPlP0P_O1RqPOPNPJO1RrPmP0P`O1RsPlP0PaO1RtPOg00R;Ru#jRv%iuRu1h35Rw%g3Rx%f3Ry1e3?R?;8?203y;R;P0P4g00TYRzg00U9R{'d20204=<z{dB01315H00R{b6b7b8X23S041000^23S05P0fRRzO1R|b4b1b1b1b0b0b0b0bKbLPZPgPGPjPkPnPoPmPpPlPqPOPrPmPsPlPtPOPvPuPwPx1H3T,G?R}=8y}P;P{b6b7b8X23130TR~/0~^23P|b4b1b1b1b0b0b0b0bKbLM9UPZPgPGPjPkPnPoPmPpPlPqPOPrPmPsPlPtPOPvPuPwPxPy1H31S06=8y?S07%|:R:Q07CDP;P{b6b7b8X23S08Q00P>[^23S09P0PzfPR>O2b4b1b1b1b0b0b0b0bKbLPZPgPGPjPkPnPoPmPpPlPqPOPrPmPsPlPtPOPvPuPwPxPy1H3A,G?Rt1H3C%{F5z3RF58yS0:P:A8y}FCDP;P{b6b7b8X23130AR}/0HRs135T/0H[^23P0PzfORqO2b4b1b1b1b0b0b0b0bKbLP0M9yC:WQWMP5P0O2n2001000000121000000W3WIWHXE3P0O1PIPJ1RcKR|#T%M|CKAV<86=<=KPL[^G3^E3^F3PMPIP[P6PTPMPIP[PDP7PMPIP[PEP4PYP7P6PWP6P6PXP6PCPIP4P6PNPIP4P6O3E6D7CSE2E2E@P2PMPIPBP8PTD`PMPIPBPDP6PMPIPBPEP7PUP6P8PWP8P8PXP8PCPIP7P8PNPIP7P8O3E6D7CSE2E2PMPJfIR7P<PTPMPJP7PDP8PMPJP7PEP6Q02P8P<PWP<P<PXP<PCPJP6P<PNPJP6P<O3E6D7CSE2E2E@P0PMPIfJR6P9PTD`PMPIfKRUPDP9PMPIPUPEP<Q03P9PQPWPQPQPXPQPCPIP<PQPNPIP<PQO3E6D7CSE2E2P2PMPIfLRYPDPQDQPMPIPYPEP9PQ14Q\PWP\P\PXP\PCPIP9P\PNPIP9P\O3E6D7G?PMPJfMRLPSPTPMPJPLPDP\PMPJPLPEPQP\14\SPWPSPSPXPSPCPJPQPSPNPJPQPSO3E6D7G?E2E@P0PMPIfNRKPDPSDQPMPIPqPEPSP]14]_PWP_P_PXP_PCPIPSP_PNPIPSP_O3E6D7G?P2PMPIP>PEP]DQP_P_P^PWP^P^PXP^PCPIP]P^PNPIP]P^O3E6D7C_PMPJfQRSP`PTPMPJPSPDP^PMPJPSPEP_P^14^`PWP`P`PXP`PCPJP_P`PNPJP_P`O3E6D7G?E2E@P0PMPIPzPEP^DQPaPaPdPWPdPdPXPdPCPIP`PdPNPIP`PdO3E6D7C_P214db,NdPWPbPbPXPbPCPIPaPbPNPIPaPbO3E6D7PMPJfURaPePTPMPJPaPDPbPMPJPaPEPdPb14bePWPePePXPePCPJPdPePNPJPdPeO3E6D7G?E2E@P014eV,NePWPPPPPXPPPCPIPePPPNPIPePPO3E6D7P210cX9LWcPcPCPIPVPcPNPIPVPcO3E6PMPJfYRVPRPTPMPJPVPDPcPMPJPVPEPPPc14cRPWPRPRPXPRPCPJPPPRPNPJPPPRO3E6D7G?E2E@P010[X9LW[PBPCPIPRPBPNPIPRPBO3E6P21O7CPIP[P7PNPIP[P7O3C^PMPJf]R[P6PTPMPJP[PDP7PMPJP[PEPBP71476PWP6P6PXP6PCPJPBP6PNPJPBP6O3E6D7G?E2E@P01OUCPIP6PYPNPIP6PYO3C^P2A;IULPNPIPUPLO3PMPJfaRUPKPTPMPJPUPDPLPMPJPUPEPYPL14LKPWPKPKPXPKPCPJPYPKPNPJPYPKO3E6D7G?E2E@P0A;ILqPNPIPKP>O3PMPJfdRY13STRTC>PMPJ13YDS03P>C>S02PMPJ13YES0;PqC>S0<14>S,N>S0=10SX9LWSS0>1OSCS0?A;JqSS0@PNPJPqPSO3S0A'1S0B'1S0C'1S0D'1S0E'1S0F'1PMPIPJPYPTPIPJPYPAPYPDPKPZPgPGPj1\C@RT%5@141X[\fRNA[C@5ViXJhR@%5X\i^JhRi1uaCRX%5afWRa/CCRW#5\h[RhfV/tCRU%]CR6#s1WaC,BC/3W9<3a[RW1raCRafXRB/CCRR14RC'N\fRf1qBCRB14C11CVCRR,4C?IR1[RR1wVCRVfZR1/WC#]\6RP1x1CR1f[Re/CC=<3e\6R61WeCReP3f\Rd/CCRCP3P2%5dR`14d[RdfqR[/0[P7f^#5Rzf_f`'4R_PkPnP0P<O1R<PmP0P9O1R9PlP0PQO1RQPOPrPmPoPlPpPOQ04Q05P0f|S05O1S04b4b1b1b1b0b0b0b0W=W<P5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd13[DR|13[AS0G'0P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPx1H3DS0H,G?R~=8ytP;P{b6b7b8X23130DS0I/0}^23Q04b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBM9UPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd%5[P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOQ08Q09P0Q05fzO2S09b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd10|HP7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxPyQ0:P:A8y~FCDP;P{b6b7b8X23135DS08/0H\s^23P0Q05fyO2S05b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000121000000bDbCb;b:b9b5b3b>b?b@bAbBP7M9XQ02Q0FPMPIPJQ03P>PIPJPYPAQ03PDPKPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd10[|P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxA8y?~P;P{b6b7b8X23Q0I,00^23Q04b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd13|DS03Q0G'0P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxQ0H,G~S0F=8ytP;P{b6b7b8X23Q0I/3D/0}^23Q04b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBM9UPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd%5|P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxPyQ07P:Q06=8y~CDP;P{b6b7b8X23Q00Q08#5[^23Q09b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`PdQ03/0HP7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxPyQ0:P:Q0F=8yFCDP;P{b6b7b8X23Q08/3D/0H\s^23Q05b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000121000000bDbCb;b:b9b5b3b>b?b@bAbBPcM9XQ0<Q0EPMPIPJQ0;PqPIPJPYPAQ0;PDPKPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd13[ERK,0[P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPx1H3E,G?R[98y?P;P{b6b7b8X23130ER?,00^23Q04b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd13KDRAQ0G'0P7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxQ0H,G[RY=8ytP;P{b6b7b8X2313?D/0}^23Q04b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBM9UPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd%5KP7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxPyQ07P:Q06=8y[CDP;P{b6b7b8X23Q00135ERE#5[^23Q09b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000120000000bDbCb;b:b9b5b3b>b?b@bAbBPZPgPGPjPTPNP@PiPXPhPUPWPaPfPBPRPVPPP1P6PeP3PCP3P2P`Pd10AHP7PkPnP<PmP9PlPQPOPrPmPoPlPpPOPvPuPwPxPyQ0:P:A8yYFCDP;P{b6b7b8X2313ED/0H\s^23Q05b4b1b1b1b0b0b0b0X=_X<zP5P0O2n2001000000121000000bDbCb;b:b9b5b3b>b?b@bAbBPbM9XQ0=Q0DP^Q0>Q0CP\Q0?Q0BP8Q0@Q0APIPJPqPSPLPSP>PqAVS>q,d=O4P5EcQ01C:C:C:C:C:C:C:WNWSP5P0O2n2001000000121000000W3WVP5P0O2n2001000000121000000W3WUP5P0O2n2001000000121000000W3WMP5P0O2n2001000000121000000W3WZP5P0O2n2001000000121000000W3W[P5P0O2n2001000000121000000W3WYP5P0O2n2001000000121000000W3WIWHXG3XE3XF3P4P5P0O3n0110501021110031103100102P]P\P0O3C:C:W3WNP5P0O2n2001000000121000000W5WRP5P0O2n2001000000121000000W5WIWTWHWXWWXP=XO3P5P0O2WPXO3o"). Qed.

Lemma with_src_id s : PQM.with_src s (PQM.p_src s) = s.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "p'0h01sh14p_bbi004p_bbh24p_bgi014p_bgh37p_depthi027p_depthh46p_donei036p_doneh56p_morei046p_moreh64p_sbi054p_sbh74p_ski064p_skh85p_srci075p_srch95p_stki085p_stkh:4p_tbi094p_tbh;4p_tgi0:4p_tgi0;1mp;1p;2p;3p;;p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p606000p1007]p4p771111110p8P1p1008bp4p710p8g01H3j15Tg01I2j24Tg00?@j30Tg00EWj11Tg01J4l;3Tg00KRj22Tg01K4R1P1f0R0%50'4=010P0g00A\R2g01L4g01G5g01>_g00cm#1f:R3f9R4f8R5f7R6f6R7f5R8f4R9f3R:f2R;f1R<P0M;3,21W9X72X62X22W1X;2W:W8X32X42W5P3P4P5P6P7P8P9P:P;P<P0O;n0110;0001;010410310210710910:100101105106108X01P0O1W0o"). Qed.

(* [comment removed for export] *)
Lemma mparser_at_frame op ois s src' :
  0 <= op -> op + PQM.PSIZE <= 2 ^ 64 ->
  dkr M M' op PQM.PSIZE ->
  ag op 24 ->                                                            (* [comment removed for export] *)
  ag (op + PQM.OFF_SRC + 8) 232 ->                                       (* [comment removed for export] *)
  PM.src_fields_at segs T3 M' (op + PQM.OFF_SRC) ois (ois + 16) src' ->  (* [comment removed for export] *)
  ag (op + PQM.OFF_MAXD) 8 ->                                            (* [comment removed for export] *)
  ag (fst (vs_cells (op + PQM.OFF_TB) (PQM.p_tb s))) (snd (vs_cells (op + PQM.OFF_TB) (PQM.p_tb s))) ->
  (forall c n p, PQM.p_tb s = PM.VLong c n p -> dkr M M' p c) ->
  ag (op + PQM.OFF_BB) 24 -> (forall b n c, PQM.p_bb s = PQV8.V8Blk b n c -> dkr M M' b c) ->
  ag (op + PQM.OFF_STK) 24 -> 0 <= PQM.p_sb s -> PQM.p_sb s + PQM.PSZ * 2 ^ PQM.p_sk s <= 2 ^ 64 -> ag (PQM.p_sb s) (PQM.PSZ * 2 ^ PQM.p_sk s) ->
  PQM.mparser_at segs A T3 T4 vp M op ois s -> PQM.mparser_at segs A T3 T4 vp M' op ois (PQM.with_src s src').
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "p'0h04__x1h17__arithh24__ffh37__sat21h47__sat22h57__sat23h67__sat24h78__varmaph85__with91Hh:1ch;1nh<2Hah=4AGSBh>4AGTBh?2BBh@3D01hA4DKBBhB4DKTBhC2DPhD3H12hE2H8hF2H9hG2HbhH3Hb'hI3M01hJ3STKhK2TBhL1bhM1phN3oishO2ophP1shQ4src'hR3AG0hS4AGBBhT4AGMXhU3AGNhV4AGSHhW1DhX2DKhY2H0hZ3H16h[3H20h\3HMXh]2Hoh^3Ho'h_2NIh`3SRCha2_Hhb3_H0hc3_H1hd2bbhe2bghf2dnhg2dphh2mohi2sbhj2skhk3srchl3stkhm2tbhn2tgi001mi014p_bbi024p_bgi037p_depthi046p_donei056p_morei064p_sbi074p_ski085p_srci095p_stki0:4p_tbi0;4p_tgp%0p&0p;1p;2p;4p;3p;9p;;p;5p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0g001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R2p1005_p4p710p8P2P0p8P2p1006Ap4p710R2p8p1006]p606000p1007]p4p771111110p8P2p1008bp4p710p8g009@j1LTg00WXj1GTg00X6j2XTg00@3j4sTg00I=j1RTg00;Hj4PTg00<dj20Tg01M3j1KTg01@Uj2xTg01A^k30XTg00?@j3ETg01N1j1WTg01;\k30UTg01Noj1OTg01Omj1YTg01Pkl9@Tg00]Tj4lTg00V7j3]Tg01Qoj14Tg01Roj12Tg01Soj13Tg01I2j2ATg01H3j1hTg00EWk101Tg01J4l;HTg01DYj4_Tg00ZWj4VTg01U0j5rTg01V1j7eTg01B\j5bTg01<Wj6dTg01W6j1~Tg00eKj8qTg00=]R2j21Tg00^Qj2}Tg00=Aj2oTg00_9j3|Tg00DWk10STg00F7k20RTg00GQk10QTg00Gok10PTg00HZk20NTg00K0k20MTg00KRk20JTg00Klk20ITg00LXk30HTg00M7k40FTg00<Hj2DTg00_]l9\Tg00W5j2jTg00>^k10ETg009ek10BTg00`ak30ATg00bNm90@Tg01=Sk60?Tg01EUl9pTg00aDl9kTg01X5m90>Tg01YBm90CTg01ZJk80=Tg01[Wk70<Tg01\bm;0GTg00cRj4nTP1k309Tg01FXk308Tg00mRk20OTg01^0j2`Tg00JEj4zTg00Mij7{Tg00Ibj3yTg00O1k800Tg00UYR1f0R0'Dp=>%L0#Lp=Jf2R3f1R4'0/D0p==g01^J,00p=;f7R5f6R6f5R7f4R8f3R91034P0Fep=mg01_K,00p=8g01`MR:,00p=cg00A\R;@09;0p=vB08;;0p=tg01aMR<,00p>0Wg01bMR=,00p>0Tg017=00O0p=^P8P9P3104:%K0Dbp=:P5P6P7P8109=%O3%Y4%~0Gqp=61D131D40'1p=5AE;61AE;78'`AE;91AE;34'`/10'1,15p=7P6P7P8P9103<%W4Ed/10p=9P7P8P9g01cNS00CV1140,13'1p=<P5P6P7P8P9P3%h4Fe/10p=CP6P7P8P91034Dr/10p=FP5P6P7P1C_P8P91034P1CV/10'1p=NP7P81093P4CV/10p=UP7P81093P4C_/10p=M1140,13p=[P8P91034P0C_p=TP8P91034P0CVp=iP3P4P0P1C_p=wP8P91034P1CV/10p>07P9P31040P1CVp>06P7P8P9P31040Drp>05P3P4P0Q00CVp=uP7P8P9103:P4Db/10,16p>04P7P8P9P3P4Db/10p>03P7P8P9P3104<P0Edp=gAE;71AE;89'`1D131D40'1'1p=fAE;91AE;34'`/10p>02AE;31AE;40'`p=SP3P4P0P1CVp>0VP3g00P<R>g00P[R?P?g00Q;R@P;P4g00OURAP0Czg00Q[RBF{p=B1j;0p=aAy;40p=IP9P>P?P?P@P3P4P0L00p>0D1j;09y;4p=QP7P>P?P?P@P8P9P3P>P?P?P@P;P4PAP0CzPBF{L00p=?P6P7P8P9P3P4P0CnCnp=ZP8P9P3104:P0Dbp>0;P5P6P7P8109=P3P4P0Gqp>0:P6P7P8P9103<P4Ed/10p>0KP5P6P7P8P9P3P4Fe/10p>0Lg01K4S01g01L4S02Q01Q02%>9g01dQR<g00A7R=#LR:#GRB%L:S03#LRA#LR>#JRC#GRD'XRE5=8p,1MRFp,2M'RGP7P<CsPFPGP6%R=RH#JRI#L#GRJCPPFPG%;5%GARA'0%RH#L#R#L#J#GS04CPp,4segsRHp,2T3RKPGf8RL#;P5P5%G>R>P7GmPFPGf9RM#8PACPPFPGf:RN#c%KL'xRO#v%tOCPg01G5ROf<RP#KB0X340RQ3EPFPGP4P9CsRR[^M;^;;^:;PFPG&0WPPJCPg01>_RSf>RT#WB0U340RU3EPFPGP9P4CsRV[^:;^;;^L;PFPG&0TTPJCPf=RW#O#>%OT%YT,XB#^;=EPFPGf?RX#O%YX,XB#^CPPHp,1ARYPKp,2T4RZp,2vpR[PFfBR\fAR]f@R^M9@P2PHPFfCR_P[ClA]F_<PKPFP_PJO3PHPFP_PA%4]R`PHPFP_Q03#R#GRa%2]RbPHPFP_%GIRc%3]RdPHPF10_>PHPFP_%R:R:#JRe#GRfPHPYPKPF%;_RgPAPHPKPFPgP\10\>P]PHPF%8_RgPKPFPgPAO3PHPKPFP_P]D:PHPKPZPFP_P]PHPKPZPFP_P]P]P]G6P`P`%G=R`PbPbP`Q00/0`Rb95ddG7F9E<GCFFGNEUEMEM3[PHPYPKPZP[PGfDRdP_1A\]M9@P0PHPFfERgP[ClfFRh=]F<PKPFPhPJO3PHPFPhPA%4dRiPHPFPhPa%2dRjPHPFPhPc%3dRkPHPF10h>RlPHPFPhPfPHPYPKPF%;hRmPAPHPKPFPmPg10g>PdPHPF%8hRmPKPFPmPAO3PHPKPFPhPdD:PHPKPZPFPhPdPHPKPZPFPhPdPdPdG6PiPiP`PjPjP`A5kkbG7F9E<GCFFGNEUEMEM3[P2fGRk=]F<PKPFPkPJO3PHPFPkPA%4gRjDTPHPFPkPa%2gRiPHPFPkPc%3gRmPHPF10k>PHPFPkPfPHPYPKPF%;kRnPAPHPKPFPnPhPlPgPHPF%8kRlPKPFPlPAO3PHPKPFPkPgD:PHPKPZPFPkPgPHPKPZPFPkPgPgPgG6PjPjP`PiPiP`A5mmbG7F9E<GCFFGNEUEM3[PHPYPKPZP[PGfHRmPk1AhgM9@P0fIRi=]F<PKPFfJRjPJO3PHPFPjPA%4mRlDTPHPFPjPa%2mRnPHPFPjPc%3mRoPHPF10j>RpPHPFPjPfPHPYPKPF%;jRqPAPHPKPFPqPi10i>PmPHPF%8jRqPKPFPqPAO3PHPKPFPjPmD:PHPKPZPFPjPmPHPKPZPFPjPmPmPmG6PlPlP`PnPnP`A5oobG7F9E<GCFFGNEUEM3[P2PKPFfKRoPJO3PHPFPoPA%4iRnPHPFPoPa%2iRlPHPFPoPc%3iRqPHPF10o>PHPFPoPfPHPYPKPF%;oRrPAPHPKPFPrPjPpPiPHPF%8oRpPKPFPpPAO3PHPKPFPoPiD:PHPKPZPFPoPiPHPKPZPFPoPiPiPiG6PnPnP`PlPlP`A5qqbG7F9E<GCFFGNEUEMEMPHPYPKPZP[PGfLRqPo1AjiM9@P0PKPFfMRjPJO3PHPFfNRoPA%4qRlPHPFPoPa%2qRnPHPFPoPc%3qRpPHPF10o>RrPHPFPoPfPHPYPKPF%;oRsPAPHPKPFPsPj10j>PqPHPF%8oRsPKPFPsPAO3PHPKPFPoPqD:PHPKPZPFPoPqPHPKPZPFPoPqPqPqG6PlPlP`PnPnP`A5ppbG7F9E<GCFFGNEUEMEMP2PHPFfORpPA%4jRnDTPHPFPpPa%2jRlPHPFPpPc%3jRqPHPF10p>PHPFPpPfPHPYPKPF%;pRsPAPHPKPFPsPoPrPjPHPF%8pRrPKPFPrPAO3PHPKPFPpPjD:PHPKPZPFPpPjPHPKPZPFPpPjPjPjG6PnPnP`PlPlP`A5qqbG7F9E<GCFFGNEUEMPHPYPKPZP[PGfPRqPp1AojM9@P0PHPFfQRoPA%4pDTPHPFfRRpPa%2qRjPHPFPpPc%3qRlPHPF10p>RnPHPFPpPfPHPYPKPF%;pRrPAPHPKPFPrPo10o>PqPHPF%8pRrPKPFPrPAO3PHPKPFPpPqD:PHPKPZPFPpPqPHPKPZPFPpPqPqPqG6%4qRqPqP`PjPjP`A5llbG7F9E<GCFFGNEUEMP2PHPFfSRlPa%2oRjDTPHPFPlPc%3oRqPHPF10l>PHPFPlPfPHPYPKPF%;lRrPAPHPKPFPrPpPnPoPHPF%8lRnPKPFPnPAO3PHPKPFPlPoD:PHPKPZPFPlPoPHPKPZPFPlPoPoPoG6%4oRnPnP`PjPjP`A5qqbG7F9E<GCFFGNEUPHPYPKPZP[PGfTRqPl1ApoM9@P0PHPFfURpPa%2lDTPHPFfVRlPc%3qRoPHPF10l>RjPHPFPlPfPHPYPKPF%;lRnPAPHPKPFPnPp10p>PqPHPF%8lRnPKPFPnPAO3PHPKPFPlPqD:PHPKPZPFPlPqPHPKPZPFPlPqPqPqG6%4qRnPnP`%2qRqPqP`A5oobG7F9E<GCFFGNEUP2PHPFfWRoPc%3pRqDiPHPF10o>PHPFPoPfPHPYPKPF%;oRnPAPHPKPFPnPlPjPpPHPF%8oRjPKPFPjPAO3PHPKPFPoPpD:PHPKPZPFPoPpPHPKPZPFPoPpPpPpG6%4pRjPjP`%2pRjPjP`A5qqbG7F9E<GCFFGNPHPYPKPZP[PGfXRqPo1AlpM9@P0PHPFfYRlPc%3oDiPHPFfZRo/0>RpPHPFPoPfPHPYPKPF%;oRjPAPHPKPFPjPl10l>PqPHPF%8oRjPKPFPjPAO3PHPKPFPoPqD:PHPKPZPFPoPqPHPKPZPFPoPqPqPqG6%4qRjPjP`%2qRjPjP`%3qRq?5qbG7F9E<GCFFGNP2f[Rq/0>9wHFPHPFPqPfPHPYPKPF%;qRjPAPHPKPFPjPoPpPlPHPF%8qRpPKPFPpPAO3PHPKPFPqPlD:PHPKPZPFPqPlPHPKPZPFPqPlPlPlG6%4lRpPpP`%2lRpPpP`%3lRp?5pbG7F9E<GCFFI07PHPYPKPZP[PGf\RpPq1AolM9@P0f]Ro/0>Rl9wHFPHPFf^RqPfPHPYPKPF%;qRjPAPHPKPFPjPoPlPpPHPF%8qRlPKPFPlPAO3PHPKPFPqPpD:PHPKPZPFPqPpPHPKPZPFPqPpPpPpG6%4pRlPlP`%2pRlPlP`%3pRp?5pbG7F9E<GCFFI07P2PHPFf_RpPfH06PHPYPKPF%;pRlPAPHPKPFPlPq10q>PoPHPF%8pRlPKPFPlPAO3PHPKPFPpPoD:PHPKPZPFPpPoPHPKPZPFPpPoPoPoG6%4oRlPlP`%2oRlPlP`%3oRl?5lbG7F9E<GCFFPHPYPKPZP[PGf`RlPp1AqoM9@P0PHPFfaRqPfH06PHPYPKPFfbRp#;RjPAPHPKPFPjPq10q>PlPHPF%8pRjPKPFPjPAO3PHPKPFPpPlD:PHPKPZPFPpPlPHPKPZPFPpPlPlPlG6%4lRjPjP`%2lRjPjP`%3lRl?5lbG7F9E<GCFFP2PHPYPKPFfcRl#;RjPAJ05PHPKPFPjPp10p>PqPHPF%8lRjPKPFPjPAO3PHPKPFPlPqD:PHPKPZPFPlPqPHPKPZPFPlPqPqPqG6%4qRjPjP`%2qRjPjP`%3qRj?5jbG7F9E<GCPHPYPKPZP[PGfdRjPl1ApqM9@P0PHPYPKPFfeRp#;PAJ05PHPKPFffRl#;Pp10p>PjPHPF%8lRnPKPFPnPAO3PHPKPFPlPjD:PHPKPZPFPlPjPHPKPZPFPlPjPjPjG6%4jRnPnP`%2jRnPnP`%3jRj?5jbG7F9E<GCP2PHPKPFfgRj#;PlPlP>%hpGmPHPF%8jRnPKPFPnPAO3PHPKPFPjPpD:PHPKPZPFPjPpPHPKPZPFPjPpPpPpG6%4pRnPnP`%2pRnPnP`%3pRn?5nbG7F9E<PHPYPKPZP[PGfhRnPj1AlpM9@P0PHPKPFfiRl#;PnPnP>%hjGmPHPFfjRj#8RrPKPFPrPAO3PHPKPFPjPnD:PHPKPZPFPjPnPHPKPZPFPjPnPnPnG6%4nRrPrP`%2nRrPrP`%3nRn?5nbG7F9E<P2fkRn#8Rr9uHFPKPFPrPAO3PHPKPFPn%KlPHPKPZPFPnPlPHPKPZPFPnPlPlPlG6%4lRrPrP`%2lRrPrP`%3lRr?5rbG7F9K04PHPYPKPZP[PGflRrPn1AjlM9@P0fmRj#89uHFPKPFfnRl#8PAO3PHPKPFPl%KrPHPKPZPFPlPrPHPKPZPFPlPrPrPrG6%4rRnPnP`%2rRnPnP`%3rRr?5rbG7F9K04P2PKPFfoRr#8PAO3PHPKPF%cr%KjPHPKPZPFPrPjPHPKPZPFPrPjPjPjG6%4jRnPnP`%2jRnPnP`%3jRn?5nbG7F9J03PHPYPKPZP[PGfpRnPr1AljM9@P0PKPFfqRj#8PAO3PHPKPFfrRr#c%KnPHPKPZPFPrPnPHPKPZPFPrPnPnPnG6%4nRsPsP`%2nRsPsP`%3nRn?5nbG7F9J03P2PHPKPFfsRnPjD:PHPKPZPFPnPjPHPKPZPFPnPjPjPjG6%4jRsPsP`%2jRsPsP`%3jRs?5sbG7F9PHPYPKPZP[PGftRsPn1ArjM9@P0PHPKPFfuRrPnD:PHPKPZPFfvS05PsPHPKPZPFQ05PsPsPsG6%4sRnPnP`%2sRnPnP`%3sRs?5sbG7F9P2PHPKPZPFfwS06%WrEgPHPKPZPFQ06PrPrPrG6%4rRsPsP`%2rRsPsP`%3rRs?5sbG7PHPYPKPZP[PGfxRsQ06Q05/ArM9@P0PHPKPZPFfyRnQ06#WEgPHPKPZPFfzS07PsPsPsG6%4sRjPjP`%2sRjPjP`%3sRs?5sbG7P2PHPKPZPFf{S08PnPnPnG6%4nRsPsP`%2nRsPsP`%3nRsPsPbEfH02PHPYPKPZP[PGf|RsQ08Q07/AnM9@P0PHPKPZPFf}RjQ08Q08Q08G6%4sRtPtP`%2sRtPtP`%3sRtPtPbEfH02P2%4jRt?St`%2jRtPtP`%3jRtPtPbEfPHPYPKPZP[PGp+01ARtp+01@Ruf~S09/AjM9@P0%4uRu?Su`%2tRuPuP`%3tRtPtPbEfP2p+01BR2#2Rt?St`%32Rt?5tbPHPYPKPZP[PGp+01ERtp+01DRup+01C/A2M9@P0%2uRu?Su`%3tRt?5tbQ01PFPGp+01I#c%K0'xRt#v%ttCP%K8=EOQPR[^M;^;;^:;%W7=ESUPV[^:;^;;^L;%O9#>%O8%Y8,XB#^;=EPFPG%O7%Y7,XB#^CPPHPFp+01OPA%46DTPHPFp+01PPa%25DTPHPFp+01QPc%3LDiPHPKPFp+01RPMD:PHPKPZPFp+01SS0:%WNEgPHPKPZPFp+01Tf;RtPtPtG6%4PRu?Su`%2WRu?Su`%3TRu?5ubPHPYPKPZP[PGp+01Xp+01WS0;p+01U,AXM9@]C]@]I]J]?]K]D]F]E]=]H]G]A]B]>p+01FQ02g00cm$01PFPGp+01^S0<#cPNPMPLP5P6P7P8P9P3P4P0M;H#K'xRu#v%tuCPPTPWPPPtPNPMPLP5P6P7P8M;HRu#K=EOQPR[^M;^;;^:;PXPTPWPPPtPNPMPLP5P6P7M;HRR#W=ESUPV[^:;^;;^L;PWPPPtPNPMPLP5P6P7P8P9M;H#O#>%Ou%Yu,XB#^;=EPFPG%OR%YR,XB#^CPPHPFp+01dS0=PAP^PXPTPWPPPtPNPMPLP5P6M;H#4DTPHPFp+01eS0>PaP]P^PXPTPWPPPtPNPMPLP5M;H#2DTPHPFp+01fRRPcP\P]P^PXPTPWPPPtPNPMPLM;H#3DiPHPKPFp+01gS0?P_P\P]P^PXPTPWPPPtPNPMM;HD:PHPKPZPFp+01hPdP_P\P]P^PXPTPWPPPtPNM;H#WEgPHPKPZPFp+01iPgPdP_P\P]P^PXPTPWPPPtM;HRuPuPuG6PhPgPdP_P\P]P^PXPTPWPPM;H#4Ru?Su`PkPhPgPdP_P\P]P^PXPTPWM;H#2Ru?Su`PmPkPhPgPdP_P\P]P^PXPTM;H#3Ru?5ubPHPGp+01mRuP[ClS0@%RI#J#J#GRI9]GuS0APKPGPuPJO3S0BPHPG10uAS0CPiPmPkPhPgPdP_P\P]P^PXM;Hp+01j'ARX#4S0DC_S0EPHPG10uaS0F%2XS0GC_S0HPHPG10ucS0I%3XS0JCVS0K10u>S0L9wHGS0M10ufS0N:0VHGS0OPHPYPKPG10uJRd/0AS0PDrS0QPHPKPGPdp+01lS0RQ0R/0>S0S%hXS0TFeS0U%Je#J#GRd,0uS0V9uHGS0WPKPGQ0VPAO3S0XPHPKPG%Re#L#J#GRe,0uS0Y%KXS0ZDbS0[PHPKPZPG%R:R:#L#J#J#GS0\,0uS0]%WXS0^EdS0_PHPKPZPG%R:#R#L#J#GS0`,0uS0a%OXS0b%YXS0c%~XS0dGqS0eQ0DQ0D;S`S0fQ0GQ0G;S`S0gQ0JQ0J;5bS0h'1S0i'1S0j'1S0k'1S0l'1S0m'1S0n'1S0o'1S0p'1S0q'1S0r'1S0s'1S0t'1S0u'1S0v'1S0w'1S0xPHPFPGPuP[PFPGPuPJPuPAPR1}B^R^1o1BRb%>]1XB\,o1[[R\%>BR:g00doRgA|B_4UW<Rh1XB_#>\g^<:R_1}BDRk%>D1o1E[\bRbA|BD4VgX<:RD%>E\g^<:R:g00R;Rg$0SRm&01gRg20R;4Ri&0Q;RV&0P;RU20N;=R=;B=20MU@R@P0P3g00TYRQg00U9R2+0J20I03=EQ2dB0H;14H0FR2b2b7b8X0;1D00^0;P0p+022RQO1Rjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPV%aAS0y,I=Rv%aJRw,I=Rx5BUP@P2b2b7b8X0;100AS0z100JRy'D^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPU1j;1Rz=BU=R{&0E?R?P{H0DP@P2b2b7b8X0;%>0R|%>4[^0;P0PQp+01nO2R}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPU1Q=IS0{%aB&0BC60A;RC5BURBP?PUPvPCE?P@P2b2b7b8X0;100IS0|/DER~104AS0}/DE[^0;P0PQPuO2RQb1b3b4b5b6Q0;N90@Q0AQ0wPFPGPuPIQ0?Q0:J0?Q0BQ0vg01:cS0vQ0EQ0uPHPFPGQ0CQ0DPFPGPuPJQ0CP`PRP^P\PhP_PkPbPDP:PmPgPiPVABU=vP@P2b2b7b8X0;Q0z,D0^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPV%a`S0C,IvS0D=BUxP@P2b2b7b8X0;Q0z?=`y^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzPvE?P@P2b2b7b8X0;Q0}#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUQ0DPCE?P@P2b2b7b8X0;Q0}?=`E\~^0;PQb1b3b4b5b6PLM9pQ0HQ0tPHPFPGQ0FQ0GPFPGPuPJQ0FP`PRP^P\PhP_PkPbPDP:PmPgPiPV1Q=aRv9BU=P@P2b2b7b8X0;100aS0F,D0^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVQ0C,IvS0G=BUxP@P2b2b7b8X0;Q0F?=`y^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzPvE?P@P2b2b7b8X0;104aRa#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUQ0GPCE?P@P2b2b7b8X0;A=a`E\~^0;PQb1b3b4b5b6P5M9pQ0KQ0sPHPFPGQ0IQ0JPFPGPuPJQ0IQ03#GRaPRP^P\PhP_PkPbPDP:PmPgPiPV1Q=cS039BU=P@P2b2b7b8X0;100cS0I,D0^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVQ03%aaRv'IS0J=BUxP@P2b2b7b8X0;Q0I?=ay^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzQ03E?P@P2b2b7b8X0;104cRc#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUQ0JPCE?P@P2b2b7b8X0;A=caE\~^0;PQb1b3b4b5b6P6M9kQ0MQ0rPHPFPGQ0LP1PFPGPuPJQ0LP`PRP^P\PhP_PkPbPDP:PmPgPiPV1Q=>Rc9BU=P@P2b2b7b8X0;100>S0L,D0^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVQ0C,IcS0C=BUxP@P2b2b7b8X0;Q0L?=`y^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzPcE?P@P2b2b7b8X0;104>R>#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUQ0CPCE?P@P2b2b7b8X0;A=>`E\~^0;PQb1b3b4b5b6Q09M9pQ0OQ0qPHPFPGQ0NP1PFPGPuPJQ0NPaPRP^P\PhP_PkPbPDP:PmPgPiPV1Q=fRR9BU=P@P2b2b7b8X0;100fR1,D0^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPV1IRvR>=BUxP@P2b2b7b8X0;A=1ay^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzPRE?P@P2b2b7b8X0;104fRf#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUP>PCE?P@P2b2b7b8X0;A=faE\~^0;PQb1b3b4b5b6Q07M9kQ0QQ0pPHPYPFPGQ0PP^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzQ0y,IxRxE?P@P2b2b7b8X0;104J/0ARf#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUQ04,QxPCE?P@P2b2b7b8X0;Q04==fE\~^0;PQb1b3b4b5b6Q0>Q05N90>Q0UQ0oQ0=Q0WQ0nPHPFPGQ0VQ00PFPGQ0VPAQ0VPap+01cP^P\PhP_PkPbPDP:PmPgPiPV1Q=dRf=BUfP@P2b2b7b8X0;100dRx/Dx^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPV1IfvRvQ0y,If5BUP@P2b2b7b8X0;10xA9=xa^0;Pjb1b3b4b5b6M9\P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzPfE?P@P2b2b7b8X0;104dRd#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PUPvPCE?P@P2b2b7b8X0;A=daE\~^0;PQb1b3b4b5b6PlM9kQ0XQ0mQ0vQ0[Q0lQ0YQ0ZP^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPz1Q=eRlE?P@P2b2b7b8X0;104eRd#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PU1IlwRaPCE?P@P2b2b7b8X0;A=dJE\~^0;PQb1b3b4b5b6PTPFPGPuPIQ0YPJQ0?P^P\PhP_PkPbPDP:PmPgPiPVABU=lP@P2b2b7b8X0;100eRe,D0^0;Pjb1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVQ0{9BUaP@P2b2b7b8X0;Q0|9=eJ^0;Pjb1b3b4b5b6N90CPWP7L0=Q0_Q0kQ0]Q0^P^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzQ0\,Q=RjE?P@P2b2b7b8X0;Q0\,04Re#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PU1IjwPCE?P@P2b2b7b8X0;A=eJE\~^0;PQb1b3b4b5b6p+01`PPP8K0<Q0eQ0jQ0aQ0bQ0cQ0dP^P\PhP_PkPbPDP:PmPgPiPVPUP{P?PUPzQ0`,Q=R=E?P@P2b2b7b8X0;Q0`,04Rz#>\|^0;P}b1b3b4b5b6P^P\PhP_PkPbPDP:PmPgPiPVPUPBP?PU1I=wPCE?P@P2b2b7b8X0;A=zJE\~^0;PQb1b3b4b5b6PtPNQ0<PMP9N;0GQ0fQ0iP3Q0gQ0hP4P0CnFZFZFZFZFZFZFZFZQ0@Q0x'1eQ0@A]Gu<Q0BQ0EQ0HQ0KQ0MQ0OPHPYPKPG%;uR<PAPHPKPGP<Q0RQ0SQ0TPHPG%8uR<PKPGP<PAO3PHPKPGPuQ0ZI0;PHPKPZPGPuQ0^PHPKPZPGPuQ0bQ0cQ0dL0:Q0j'1K0KE<L0LFF3[3[3[3[ePHPYPKPZP[PGPuQ0RPXM9@RXePXeWCW@WIWJW?WKWDWFWEW=WHWGWAWBW>WlXj;Xi;Xe;XdSXn;XmOWkXg;Xf;Xh;PNPMPLP5P6P7P8P9P3P4P0O;n011000101;110510410310810:10;101102106107109PsQ08PnQ06Q05PrPpPqPoP]PWPMP7P4P0O?WCW@P4P0O2n2001000000121000000W9WIP4P0O2n2001000000121000000W9WJP4P0O2n2001000000121000000W9W?P4P0O2n2001000000121000000W9WKP4P0O2n2001000000121000000W9WcP4P0O2n2001000000121000000W9W\P4P0O2n2001000000121000000W9WbP4P0O2n2001000000121000000W9W_P4P0O2n2001000000121000000W9W[P4P0O2n2001000000121000000W9WZP4P0O2n2001000000121000000W9WDP4P0O2n2001000000121000000W9WFP4P0O2n2001000000121000000W9WEP4P0O2n2001000000121000000W9WaP4P0O2n2001000000121000000W9WWP4P0O2n2011000000121000000W9WYP4P0O2n2011000000121000000W9W=WHWGWVWAWSWBW>WTW`WUWRWXW^W]WQWPXN;XO;P9P3P4P0O4WQWPXN;XO;o"). Qed.

(* [comment removed for export] *)
Lemma mparser_at_frame_gen op ois s src' tb' tg' bb' bg' :
  0 <= op -> op + PQM.PSIZE <= 2 ^ 64 ->
  dkr M M' op PQM.PSIZE -> ag op 24 -> ag (op + PQM.OFF_SRC + 8) 232 ->
  PM.src_fields_at segs T3 M' (op + PQM.OFF_SRC) ois (ois + 16) src' ->
  ag (op + PQM.OFF_MAXD) 8 ->
  PM.vstr_at segs T3 M' (op + PQM.OFF_TB) tb' ->
  PQV8.v8_at segs T3 T4 M' (op + PQM.OFF_BB) bb' ->
  ag (op + PQM.OFF_STK) 24 -> 0 <= PQM.p_sb s -> PQM.p_sb s + PQM.PSZ * 2 ^ PQM.p_sk s <= 2 ^ 64 -> ag (PQM.p_sb s) (PQM.PSZ * 2 ^ PQM.p_sk s) ->
  PQM.mparser_at segs A T3 T4 vp M op ois s ->
  PQM.mparser_at segs A T3 T4 vp M' op ois
    (PQM.MPST (PQM.p_more s) (PQM.p_done s) (PQM.p_depth s) src' tb' tg' bb' bg' (PQM.p_sb s) (PQM.p_sk s) (PQM.p_stk s)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "p'0h04__x1h17__arithh24__ffh37__sat21h47__sat22h57__sat23h67__sat24h78__varmaph85__with91Hh:2Hah;4AGSBh<2BBh=3D01h>2DPh?3H12h@2H8hA2H9hB2HbhC3Hb'hD3M01hE3STKhF2TBhG3bb'hH3bg'hI3oishJ2ophK1shL4src'hM3tb'hN3tg'hO3AG0hP4AGMXhQ3AGNhR4AGSHhS3BB'hT1DhU2DKhV2H0hW3H16hX3H20hY3HMXhZ2Hoh[3Ho'h\2NIh]3SRCh^3TB'h_2_Hh`3_H0ha3_H1hb2bbhc2bghd2dnhe2dphf2mohg2sbhh2skhi3srchj3stkhk2tbhl2tgi001mi014p_bbi024p_bgi037p_depthi046p_donei056p_morei064p_sbi074p_ski085p_srci095p_stki0:4p_tbi0;4p_tgp%0p&0p;1p;2p;4p;9p;3p;;p;5p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p606000p1007]p4p771111110p8P1p1008bp4p710p8g009@j1MTg00WXj1HTg00X6j2UTg00@3k40MTg00I=j1RTg00;Hj4ZTg00<dj20Tg01Noj18Tg01Omj1;Tg01Pkl9?Tg00]Tj4qTg00V7j3^Tg01Qoj13Tg01Roj11Tg01Soj12Tg01W6j1@Tg01J4l;5Tg01H3j1iTg01M3j1]Tg01N1j1\Tg00EWj1|Tg01DYj4WTg00ZWj4STg01U0j5rTg01V1j7dTg01B\j5cTg01<Wj6_Tg00eKj8hTg00=]R1j24Tg00^Qj2{Tg00=Aj2pTg00_9j3zTg00DWk10KTg00F7k20JTg00GQk10ITg00Gok10HTg00HZk20GTg00K0k20FTg00KRk20ETg00Klk20CTg00?@j3NTg00LXk30BTg00M7k40ATg00<Hj2ITg00_]l9YTg00W5j2nTg00>^k10@Tg009ek10>Tg00`ak30=Tg00bNm90<Tg01=Sk60;Tg01EUl9lTg00aDl9kTg01X5m90:Tg01\bm;09Tg00cRj4mTg00mRk205Tg01^0j2bTg00JEj4xTg00Mij7yTg00Ibk302Tg00O1j8wTg00UYR0f0R2'Ip=C%M2#Mp=Jf2R3f1R4'0/I2p=Bg01^J,02p==f7R5f6R6f5R7f4R8f3R91034P2Fdp=og01_K,02p=:P8P9P3g01`MR:,04P2Dcp>04P7P8P9P3g01aMR;,04P2E_p=fg01bMR<,02p>0Ng017=0052p=[P8P9P3104:%]2Dcp=>P5P6P7P8109<%83%;4%@2Ghp=71I031I42'4p=6g00A\R=?N60AN=78'bAN=90AN=34'b/42'4,45p=9P6P7P8P9103;%\4E_/42p=<P7P8P9g01cNS00CS1442,43'4p=AP5P6P7P8P9P3%i4Fd/42p=DP6P7P8P91034Dr/42p=FP5P6P7P0CWP8P91034P0CS/42'4p=LP7P81093P4CS/42p=QP7P81093P4CW/42p=K1442,43p=gP8P91034P2CWp=PP8P91034P2CSp=jP3P4P2P0CWp=vP8P91034P0CS/42p>03P9P31042P0CSp>01P7P8P9P31042Drp>00P3P4P2Q00CSp=uP7P8P9103:P4Dc/42,46p=~102:p=}P7P8P9P3P4Dc/42p=tAN=70AN=89'b1I031I42'4'4p=eAN=90AN=34'b/42p=sAN=30AN=42'bp=TP3P4P2P0CSp>0LP3g00P<R:g00P[R>P>g00Q;R?P=P4g00OUR@P2Cxg00Q[RAFyp=G1n=2p=`B02=42p=OP9P:P>P>P?P3P4P2Gwp>0?1n=2:02=4p=VP7P:P>P>P?P8P9P3P:P>P>P?P=P4P@P2CxPAFyGwp=EP6P7P8P9P3P4P2CmCmp=XP6P7P8P9P3P4E_/42p>081442,43,49,48p=aP5P6P7P8109<P3P4P2Ghp>07P6P7P8P9103;P4E_/42p>0DP5P6P7P8P9P3P4Fd/42p>06g01K4S01g01L4S02g01G5S03g01>_S04Q01Q02Q03Q04%C5f8R;g01dQR<g00A7RA#MR@#HR:%M@S05#MRB#MRC#JRD#HRE'URF3Bp,1MRGp,2M'RHf9RIP<H0MPGPHf:RJ%RARK#JRL#M#HRMCZPGPHf;RN#=%HBRB'0%RK#M#R#M#J#HS06CZp,4segsRKp,2T3ROPHf<RP#=PNPN%HCRCPIGoPGPHf=RQ#:PBCZPKPOPHf>RRPJI04PKPOp,2T4RSPHf?RTPIEfPGPHf@RU$0NPMCZ%8T#C%8U%;U,U:#[;BFPGPHfARV#8%;V,U:#[CZPKp,1ARWPOPSp,2vpRXPGfDRYfCRZfBS07M9?P1PKPGfER[PXCqA^G[<POPGP[PMO3PKPGP[PB%3ZR\PKPGP[Q05#R#HR]%1ZR^PKPGP[%HLR_%2ZR`PKPG10[CPKPGP[%R@R@#JRa#HRbPKPWPOPG%=[RcPBPKPOPGPcPY10YCPZPKPG%:[RcPOPGPcPBO3PKPOPGP[PZD>PKPOPSPGP[PZPKPOPSPGP[PZPZPZG7P\P\%HAR\P^P^P\Q00/0\R^96``G9F<EAGDFFGLEQEKEK3gPKPWPOPSPXPHfFR`P[%3Y%1Y%2YPZQ07PVPUPT%8Y%;Y%@YM;5M9?P2PKPGfGRcPXCqfHRd=^G<POPGPdPMO3PKPGPdPB%3`RePKPGPdP]%1`RfPKPGPdP_%2`RgPKPG10dCRhPKPGPdPbPKPWPOPG%=dRiPBPKPOPGPiPc10cCP`PKPG%:dRiPOPGPiPBO3PKPOPGPdP`D>PKPOPSPGPdP`PKPOPSPGPdP`P`P`G7PePeP\PfPfP\A6gg^G9F<EAGDFFGLEQEKEK3gP1fIRg=^G<POPGPgPMO3PKPGPgPB%3cRfDPPKPGPgP]%1cRePKPGPgP_%2cRiPKPG10gCPKPGPgPbPKPWPOPG%=gRjPBPKPOPGPjPdPhPcPKPG%:gRhPOPGPhPBO3PKPOPGPgPcD>PKPOPSPGPgPcPKPOPSPGPgPcPcPcG7PfPfP\PePeP\A6ii^G9F<EAGDFFGLEQEK3gPKPWPOPSPXPHfJRiPg%3d%1d%2dPcP`P[PYPZ%8d%;d%@dM;5M9?P2fKRe=^G<POPGfLRfPMO3PKPGPfPB%3iRhDPPKPGPfP]%1iRjPKPGPfP_%2iRkPKPG10fCRlPKPGPfPbPKPWPOPG%=fRmPBPKPOPGPmPe10eCPiPKPG%:fRmPOPGPmPBO3PKPOPGPfPiD>PKPOPSPGPfPiPKPOPSPGPfPiPiPiG7PhPhP\PjPjP\A6kk^G9F<EAGDFFGLEQEK3gP1POPGfMRkPMO3PKPGPkPB%3eRjPKPGPkP]%1eRhPKPGPkP_%2eRmPKPG10kCPKPGPkPbPKPWPOPG%=kRnPBPKPOPGPnPfPlPePKPG%:kRlPOPGPlPBO3PKPOPGPkPeD>PKPOPSPGPkPePKPOPSPGPkPePePeG7PjPjP\PhPhP\A6mm^G9F<EAGDFFGLEQEKEKPKPWPOPSPXPHfNRmPk%3f%1f%2fPePiPgPdPc%8f%;f%@fM;5M9?P2POPGfORcPMO3PKPGfPRdPB%3mRgPKPGPdP]%1mRiPKPGPdP_%2mRhPKPG10dCRjPKPGPdPbPKPWPOPG%=dRlPBPKPOPGPlPc10cCPmPKPG%:dRlPOPGPlPBO3PKPOPGPdPmD>PKPOPSPGPdPmPKPOPSPGPdPmPmPmG7PgPgP\PiPiP\A6hh^G9F<EAGDFFGLEQEKEKP1PKPGfQRhPB%3cRiDPPKPGPhP]%1cRgPKPGPhP_%2cRlPKPG10hCPKPGPhPbPKPWPOPG%=hRnPBPKPOPGPnPdPjPcPKPG%:hRjPOPGPjPBO3PKPOPGPhPcD>PKPOPSPGPhPcPKPOPSPGPhPcPcPcG7PiPiP\PgPgP\A6ll^G9F<EAGDFFGLEQEKPKPWPOPSPXPHfRRlPh%3d%1d%2dPcPmPkPfPe%8d%;d%@dM;5M9?P2PKPGfSRePB%3hDPPKPGfTRfP]%1lRkPKPGPfP_%2lRmPKPG10fCRgPKPGPfPbPKPWPOPG%=fRiPBPKPOPGPiPe10eCPlPKPG%:fRiPOPGPiPBO3PKPOPGPfPlD>PKPOPSPGPfPlPKPOPSPGPfPlPlPlG7%3lRiPiP\PkPkP\A6mm^G9F<EAGDFFGLEQEKP1PKPGfURmP]%1eRkDPPKPGPmP_%2eRiPKPG10mCPKPGPmPbPKPWPOPG%=mRjPBPKPOPGPjPfPgPePKPG%:mRgPOPGPgPBO3PKPOPGPmPeD>PKPOPSPGPmPePKPOPSPGPmPePePeG7%3eRgPgP\PkPkP\A6ii^G9F<EAGDFFGLEQPKPWPOPSPXPHfVRiPm%3f%1f%2fPePlPhPdPc%8f%;f%@fM;5M9?P2PKPGfWRcP]%1mDPPKPGfXRdP_%2iRhPKPG10dCRlPKPGPdPbPKPWPOPG%=dRkPBPKPOPGPkPc10cCPiPKPG%:dRkPOPGPkPBO3PKPOPGPdPiD>PKPOPSPGPdPiPKPOPSPGPdPiPiPiG7%3iRkPkP\%1iRkPkP\A6hh^G9F<EAGDFFGLEQP1PKPGfYRhP_%2cRkDjPKPG10hCPKPGPhPbPKPWPOPG%=hRgPBPKPOPGPgPdPlPcPKPG%:hRlPOPGPlPBO3PKPOPGPhPcD>PKPOPSPGPhPcPKPOPSPGPhPcPcPcG7%3cRlPlP\%1cRlPlP\A6kk^G9F<EAGDFFGLPKPWPOPSPXPHfZRkPh%3d%1d%2dPcPiPmPfPe%8d%;d%@dM;5M9?P2PKPGf[ReP_%2hDjPKPGf\Rf/0CRmPKPGPfPbPKPWPOPG%=fRiPBPKPOPGPiPe10eCPkPKPG%:fRiPOPGPiPBO3PKPOPGPfPkD>PKPOPSPGPfPkPKPOPSPGPfPkPkPkG7%3kRiPiP\%1kRiPiP\%2kRi?6i^G9F<EAGDFFGLP1f]Ri/0C9vKGPKPGPiPbPKPWPOPG%=iRlPBPKPOPGPlPfPmPePKPG%:iRmPOPGPmPBO3PKPOPGPiPeD>PKPOPSPGPiPePKPOPSPGPiPePePeG7%3eRmPmP\%1eRmPmP\%2eRm?6m^G9F<EAGDFFI03PKPWPOPSPXPHf^RmPi%3f%1f%2fPePkPhPdPc%8f%;f%@fM;5M9?P2f_Rc/0CRd9vKGPKPGf`RhPbPKPWPOPG%=hRkPBPKPOPGPkPcPdPmPKPG%:hRdPOPGPdPBO3PKPOPGPhPmD>PKPOPSPGPhPmPKPOPSPGPhPmPmPmG7%3mRdPdP\%1mRdPdP\%2mRd?6d^G9F<EAGDFFI03P1PKPGfaRdPbH01PKPWPOPG%=dRkPBPKPOPGPkPh10hCPcPKPG%:dRkPOPGPkPBO3PKPOPGPdPcD>PKPOPSPGPdPcPKPOPSPGPdPcPcPcG7%3cRkPkP\%1cRkPkP\%2cRk?6k^G9F<EAGDFFPKPWPOPSPXPHfbRkPd%3h%1h%2hPcPmPiPfPe%8h%;h%@hM;5M9?P2PKPGfcRePbH01PKPWPOPGfdRf#=RmPBPKPOPGPmPe10eCPkPKPG%:fRmPOPGPmPBO3PKPOPGPfPkD>PKPOPSPGPfPkPKPOPSPGPfPkPkPkG7%3kRmPmP\%1kRmPmP\%2kRm?6m^G9F<EAGDFFP1PKPWPOPGfeRm#=RlPBJ00PKPOPGPlPf10fCPePKPG%:mRlPOPGPlPBO3PKPOPGPmPeD>PKPOPSPGPmPePKPOPSPGPmPePePeG7%3eRlPlP\%1eRlPlP\%2eRl?6l^G9F<EAGDPKPWPOPSPXPHffRlPm%3f%1f%2fPePkPdPhPc%8f%;f%@fM;5M9?P2PKPWPOPGfgRc#=PBJ00PKPOPGfhRh#=Pc10cCPlPKPG%:hRkPOPGPkPBO3PKPOPGPhPlD>PKPOPSPGPhPlPKPOPSPGPhPlPlPlG7%3lRkPkP\%1lRkPkP\%2lRk?6k^G9F<EAGDP1PKPOPGfiRk#=PhPhPC%icGoPKPG%:kRgPOPGPgPBO3PKPOPGPkPcD>PKPOPSPGPkPcPKPOPSPGPkPcPcPcG7%3cRgPgP\%1cRgPgP\%2cRg?6g^G9F<EAPKPWPOPSPXPHfjRgPk%3h%1h%2hPcPlPmPfPe%8h%;h%@hM;5M9?P2PKPOPGfkRe#=PgPgPC%ikGoPKPGflRf#:RlPOPGPlPBO3PKPOPGPfPgD>PKPOPSPGPfPgPKPOPSPGPfPgPgPgG7%3gRlPlP\%1gRlPlP\%2gRl?6l^G9F<EAP1fmRl#:Rj9uKGPOPGPjPBO3PKPOPGPl%]ePKPOPSPGPlPePKPOPSPGPlPePePeG7%3eRjPjP\%1eRjPjP\%2eRj?6j^G9F<F~PKPWPOPSPXPHfnRjPl%3f%1f%2fPePgPkPhPc%8f%;f%@fM;5M9?P2foRc#:9uKGPOPGfpRh#:PBO3PKPOPGPh%]jPKPOPSPGPhPjPKPOPSPGPhPjPjPjG7%3jRkPkP\%1jRkPkP\%2jRk?6k^G9F<F~P1POPGfqRk#:PBO3PKPOPG%}k%]cPKPOPSPGPkPcPKPOPSPGPkPcPcPcG7%3cRgPgP\%1cRgPgP\%2cRg?6g^G9F<EtPKPWPOPSPXPHfrRgPk%3h%1h%2hPcPjPlPfPe%8h%;h%@hM;5M9?P2POPGfsRf#:PBO3PKPOPGftRl#}%]gPKPOPSPGPlPgPKPOPSPGPlPgPgPgG7%3gRjPjP\%1gRjPjP\%2gRj?6j^G9F<EtP1PKPOPGfuS08PfD>PKPOPSPGQ08PfPKPOPSPGQ08PfPfPfG7%3fRjPjP\%1fRjPjP\%2fRj?6j^G9F<PKPWPOPSPXPHfvRjQ08%3l%1l%2lPfPgPkPhPc%8l%;l%@lM;5M9?P2PKPOPGfwRcQ08D>PKPOPSPGfxRhPjPKPOPSPGPhPjPjPjG7%3jRkPkP\%1jRkPkP\%2jRk?6k^G9F<P1PKPOPSPGfyRk%\cEfPKPOPSPGPkPcPcPcG7%3cRgPgP\%1cRgPgP\%2cRg?6g^G9PKPWPOPSPXPHfzRgPk%3h%1h%2hPcPjQ08PlPf%8h%;h%@hM;5M9?P2PKPOPSPGf{Rl%\kEfPKPOPSPGf|RnPgPgPgG7%3gRoPoP\%1gRoPoP\%2gRo?6o^G9P1PKPOPSPGf}RoPlPlPlG7%3lRpPpP\%1lRpPpP\%2lRpPpP^EeCsPKPWPOPSPXPHf~RpPo%3n%1n%2nPlPgPkPhPc%8n%;n%@nM;5M9?P2PKPOPSPGp+01@RhPoPoPoG7%3pRkPkP\%1pRkPkP\%2pRkPkP^EeCsP1%3hRk?Tk\%1hRkPkP\%2hRkPkP^EePKPWPOPSPXPHp+01CRkp+01BRgp+01ARq#3%1q%2qPhPpPoPnPl%8q%;q%@qM;5M9?P2%3gRn?Tn\%1kRnPnP\%2kRnPnP^EeP1p+01DR1#1Rn?Tn\%21Rn?6n^PKPWPOPSPXPHp+01GRnp+01FRop+01ERp#3%1p%2pP1PkPgPqPh%8p%;p%@pM;5M9?P2%1oRo?To\%2nRn?6n^Q01%82#C%84%;4,U:#[;BFPGPH%83%;3,U:#[CZPKPGp+01NPB%39DPPKPGp+01OP]%18DPPKPGp+01PS09P_%27DjPKPOPGp+01QRnP6D>PKPOPSPGp+01RRo%\5EfPKPOPSPGp+01SRpP;P;P;G7%3IRh?Th\%1JRh?Th\%2NRh?6h^PKPWPOPSPXPHp+01Wp+01V%3P%1P%2Pp+01TS0:PpPoPnQ09%8P%;P%@PM;5M9?]>]=]D]E]<]F]?]A]@];]C]Bp+01HQ02Q03Q04g00cm#|PJPIP;P5P6P7P8P9P3P4P2M;5#8#CPNPJPIP;P5P6P7P8P9P3P4M;5Rn#8%;n,U:#[;BFPGPHPPPNPJPIP;P5P6P7P8P9P3M;5Rn#8%;n,U:#[CZPKPGp+01cPBPQPPPNPJPIP;P5P6P7P8P9M;5#3DPPKPGp+01dP]PRPQPPPNPJPIP;P5P6P7P8M;5#1DPPKPGp+01eS0;P_PTPRPQPPPNPJPIP;P5P6P7M;5#2DjPKPOPGp+01fS0<PUPTPRPQPPPNPJPIP;P5P6M;5D>PKPOPSPGp+01gS0=PVPUPTPRPQPPPNPJPIP;P5M;5#\EfPKPOPSPGp+01hS0>Q07PVPUPTPRPQPPPNPJPIP;M;5RnPnPnG7PZQ07PVPUPTPRPQPPPNPJPIM;5#3Rn?Tn\PYPZQ07PVPUPTPRPQPPPNPJM;5#1Rn?Tn\P[PYPZQ07PVPUPTPRPQPPPNM;5#2Rn?6n^PKPHp+01lRnPXCqS0?%RL#J#J#HS0@9^HnS0APOPHPnPMO3S0BPKPH10nBS0CP`CWS0DPKPH10n]S0EP[CWS0FPKPH10n_S0GPYCSS0H10nCS0I9vKHS0J10nbS0K:0LKHS0LPKPWPOPH10nMS0M/0BS0NDrS0OPKPOPHQ0Mp+01kS0PQ0P/0CS0Qp+01iS0RFdS0S%Ja#J#HS0T,0nS0U9uKHS0VPOPHQ0UPBO3S0WPKPOPH%Ra#M#J#H,0nS0XQ0>DcS0YPKPOPSPH%R@R@#M#J#J#H,0nS0ZQ0<E_S0[PKPOPSPH%R@#R#M#J#HS0\,0nS0]PRPQPPGhS0^AT``\S0_AT[[\S0`A6YY^S0a'4S0b'4S0c'4S0d'4S0e'4S0f'4S0g'4S0h'4S0i'4S0j'4S0k'4S0l'4S0m'4S0n'4S0o'4S0p'4PKPGPHPnPXPGPHPnPMPnPBp+01aS0q1{:QR@1p0:Ra%CR1U:T,p0[[RL%C:Rog00doRpAz:U4UW:Rh1U:U#C\p^:oRq1{:ERg%CE1p0F[\aRaAz:E4VpX:oRE%CF\p^:oRog00R;Rp$0KRk%|pRp20J=4R1&0I=Rr&0H=Rs20G=ARA;GA20Fs?R?P2P3g00TYRtg00U9Ru+0E20C23=NtudB0B=04H0ARub2b7b8X0=1I22^0=P2p+021RtO1Rvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1Pr%`BS0r,OARw%`MS0s,OARx5GsP?Pub2b7b8X0=102BS0t102MRy'I^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPs1n=0Rz=GsAR{&0@>R>P{H0?P?Pub2b7b8X0=%C2R|%C4[^0=P2PtQ0RO2R}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsQ0@,VA%`:&0>D60==RD5GsR:P>PsPwPDEEP?Pub2b7b8X0=Q0@=B2FR~104BS0u/IF[^0=P2PtQ0>O2Rtb1b3b4b5b6Q0:N90<Q0AQ0pPGPHPnQ0@p+01bQ09J0;Q0BQ0og01:cS0oQ0DQ0nPKPGPHQ0CP`PGPHPnPMQ0CP\Q0qP@PLPhPqPgPaPEPoPkPpP1PrAGsAwP?Pub2b7b8X0=Q0t,I2^0=Pvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1Pr%`\S0n,OwS0D=GsxP?Pub2b7b8X0=Q0t?B\y^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzPwEEP?Pub2b7b8X0=Q0u#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsQ0DPDEEP?Pub2b7b8X0=Q0u?B\F\~^0=Ptb1b3b4b5b6P;M9lQ0FQ0mPKPGPHQ0EP[PGPHPnPMQ0EP\Q0qP@PLPhPqPgPaPEPoPkPpP1Pr1VA]Rw9GsAP?Pub2b7b8X0=102]S0m,I2^0=Pvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrQ0n,OwS0F=GsxP?Pub2b7b8X0=Q0m?B\y^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzPwEEP?Pub2b7b8X0=104]R]#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsQ0FPDEEP?Pub2b7b8X0=AB]\F\~^0=Ptb1b3b4b5b6P5M9lQ0HQ0lPKPGPHQ0GPYPGPHPnPMQ0GQ05#HR]Q0qP@PLPhPqPgPaPEPoPkPpP1Pr1VA_S059GsAP?Pub2b7b8X0=102_S0l,I2^0=Pvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrQ05%`]Rw'OS0H=GsxP?Pub2b7b8X0=Q0l?B]y^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzQ05EEP?Pub2b7b8X0=104_R_#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsQ0HPDEEP?Pub2b7b8X0=AB_]F\~^0=Ptb1b3b4b5b6P6M9kQ0JQ0kPKPGPHQ0IP0PGPHPnPMQ0IP\Q0qP@PLPhPqPgPaPEPoPkPpP1Pr1VACR_9GsAP?Pub2b7b8X0=102CS0I,I2^0=Pvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrQ0n,O_S0n=GsxP?Pub2b7b8X0=Q0I?B\y^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzP_EEP?Pub2b7b8X0=104CRC#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsQ0nPDEEP?Pub2b7b8X0=ABC\F\~^0=Ptb1b3b4b5b6PlM9lQ0LQ0jPKPGPHQ0KP0PGPHPnPMQ0KP]Q0qP@PLPhPqPgPaPEPoPkPpP1Pr1VAbR09GsAP?Pub2b7b8X0=102bRl,I2^0=Pvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1Pr1O0wRC=GsxP?Pub2b7b8X0=ABl]y^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzP0EEP?Pub2b7b8X0=104bRb#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsPCPDEEP?Pub2b7b8X0=ABb]F\~^0=Ptb1b3b4b5b6PcM9kQ0OQ0iPKPWPGPHQ0NP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzQ0r,OxRxEEP?Pub2b7b8X0=104M/0BRb#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsQ06,VxPDEEP?Pub2b7b8X0=Q06=BbF\~^0=Ptb1b3b4b5b6p+01`PfN90:Q0SQ0hp+01_Q0VQ0gPKPGPHQ0UQ00PGPHQ0UPBQ0UP]p+01^P@PLPhPqPgPaPEPoPkPpP1PrQ0T,VARG=GsGP?Pub2b7b8X0=Q0T,02Rf/If^0=Pvb1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1Pr1OGwRwQ0r,OG5GsP?Pub2b7b8X0=10fB9Bf]^0=Pvb1b3b4b5b6M9YP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzPGEEP?Pub2b7b8X0=Q0T,04RG#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsPwPDEEP?Pub2b7b8X0=ABG]F\~^0=Ptb1b3b4b5b6PeM9kQ0WQ0fQ0oQ0YQ0ep+01]Q0[Q0dp+01\Q0^Q0cQ0]PRPQPPP@PLPhPqPgPaPEPoPkPpP1PrPsP{P>PsPzQ0\,VARAEEP?Pub2b7b8X0=Q0\,04Rz#C\|^0=P}b1b3b4b5b6P@PLPhPqPgPaPEPoPkPpP1PrPsP:P>PsQ0s,OAPDEEP?Pub2b7b8X0=ABzMF\~^0=Ptb1b3b4b5b6PNPJp+01[PIP9N;09Q0_Q0bP3Q0`Q0aP4P2CmFXFXFXFXFXFXFXFXQ0?Q0AQ0BPKPHQ0CP`P[PYQ0RQ0>Q0=Q0<Q0;PRPQPPM;5RN#3RtCWR~PKPHQ0E%1NRzCWRMPKPHQ0G%2NRFCSRuQ0JQ0LQ0OPKPOPHQ0MQ0PQ0Q%iNR?FdQ0VQ0WPKPOPHQ0X%]NRDPKPOPSPHQ0Z%\NRAPKPOPSPHQ0]%8NRs%;NR>%@NR:GhPtPtP\PzPzP\PFPFP^EeCsR^'4K08EtDaDaDaeQ0?A^Hn<Q0BP~PMPuQ0JQ0LPKPWPOPH%=nRuPBPKPOPHPuQ0PQ0QP?PKPH%:nR?POPHP?PBO3PKPOPHPnPDI04PKPOPSPHPnPAPKPOPSPHPnPsP>P:L07/4^K0DEAL06FFDaDaePKPWPOPSPXPHPnQ0PPNM9?ePKPWPOPSPXPHPnQ0PP`P[PYPZQ07PVPUPTPRPQPPM;5RP#3%1P%2PQ0RQ0>Q0=Q0<Q0;%8P%;P%@PM;5M9?eW>W=WDWEW<WFW?WAW@W;WCWBWjXh=Xg=Xc=WbXl=WkWiXe=Xd=Xf=PJPIP;P5P6P7P8P9P3P4P2O;n011000001;110510410310810:10;101102106107109PcPjQ08PmPdPiPVPQPIP7P4P2O<W>W=P4P2O2n2001000000121000000W9WDP4P2O2n2001000000121000000W9WEP4P2O2n2001000000121000000W9W<P4P2O2n2001000000121000000W9WFP4P2O2n2001000000121000000W9WaP4P2O2n2001000000121000000W9WYP4P2O2n2001000000121000000W9W`P4P2O2n2001000000121000000W9W\P4P2O2n2001000000121000000W9WXP4P2O2n2001000000121000000W9WWP4P2O2n2001000000121000000W9W?P4P2O2n2001000000121000000W9WAP4P2O2n2001000000121000000W9W@P4P2O2n2001000000121000000W9W_P4P2O2n2001000000121000000W9WTP4P2O2n2011000000121000000W9WVP4P2O2n2011000000121000000W9W;WCWBWRWSW^WPW]WQWOWUW[WZXH=WGXN=WMWLWKXI=XJ=P5P6P7P8P9P3P4P2O8XH=WGXN=WMWLWKXI=XJ=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma alvl_at_agree a x : 0 <= a -> a + 24 <= 2 ^ 64 -> ag a 24 -> PQM.alvl_at segs M a x -> PQM.alvl_at segs M' a x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "h02T4h12T3h24__x1h37__arithh44__ffh57__sat10h66__sat9h78__varmaph85__with91Hh:2Hah;1ah<1xh=2AGh>1Dh?2H0h@2H4hA2H8hB3Ha'p;1p;2p;4p;3p;9p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R1p1005_p4p710p8P1P0p8P1p1006Ap4p710R1p8p1006]p606000p1007]p4p771111110p8P1p1008bp4p710p8g00I=j1]Tg009@j14Tg00WXj1<Tg00<dj20Tg00X6j2WTg00<Hj22Tg00;Hj4PTg01ePj4?Tg01fQj1@Tg00ZWj49Tg01gOj1>Tg01hMj18Tg00=]R1j25Tg00^Qj2VTg00=Aj2DTg00_9j3UTg00DWj1TTg00EWj1STg00F7j2QTg00GQj1OTg00Goj1NTg00HZj2MTg00K0j2LTg00KRj2KTg00Klj2HTg00?@j3ITg00LXj3JTg00M7j4GTg00W5j2;Tg00Ibj3=Tg00_]l9ATg00>^j1FTg009ej1ETg00`aj3RTg00aDl9BTg00moj6\Tg00cRj4CTg00V7j3[Tg00JEj4ZTg00Mij7YTg00O1j8XTg00UYR0f0R2'2p=7f4R3f3R4f2R5f1R6'0P2C9p=3g01iL9[62p=6P5g00P<R7g00P[R8P8g00Q;R9g00A\R:P6g00OUP2CZg00Q[FYp=1P4P7P8P8P9P5P6P2GXp=:g01jIR7%76R;g00A7R<#]#4#4#4#<R=,05%4<R>#<R?%4>R>#4R@#4#4#4RA#<RB'WRC'2p,1MRDp,2M'REP4P=CPp,4segsRFPDP3P4C?P1PFPDf5R4%@3C9PFPDP4%<>R>%>3D3PFPDP4%<@R@%83D316D4'5'5PFPEf6R3P4C?P2PFPDf7RG%@3C9PFPDf8R3P>%>GD3PFPDP3P@%8GD316D3'5'5P1PFPDf9RGP>%>3D3PFPDPGP@%83D316DG'5PFPEf:R3PGC?P2PFPDf;RHP>%>3D3PFPDf<R3P@%8HD316D3'5P1PFPDf=R1P@%83D316D1PFPEf>R3P1C?P2PFPDf?P@%83D3f@R3,6DPFPEfARH%@3RIC9PFPE10H>RJ%>3RKC9RLPFPE10H@RM%83R3C9RN16EHRO'5RP'5PFPDPEPHPIPDPEPHP=PHP>P11V?BRI1D0?%7B1D0C[[RQ%7?RRg00doRSAU?B6UW:RB%7C\S^:RRRp,2T4PEO1RSp-0RT\:RU\:RV\:RWP2fDO1RXPVP2fEO1RYPUP2fFO1RZPTp,2T3PEO1R[PVP2fHR\O1R]PUP2fIR^O1R_PTg00R;R`#TRa%S`R`1Q:6Rb%O:Rc%N:Rd1M:<R<;1<1Ld9R9P2P5g00TYReg00U9Rf'K1H25=IefdAJ:06CGRfb4b7b8X2:1222^2:P2fKReO1R5b3b1b1b1b0b0b0b0b6b5PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPc1;:>Rg9=:<Rh1;:=9=:<Ri51dP9Pfb4b7b8X2:102>Rj102=Rk'2^2:P5b3b1b1b1b0b0b0b0b6b5M9APIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcPd1;:0R0=1d<Rl%F8R8PlC:P9Pfb4b7b8X2:%72RmP;[^2:P2PeP^O2R^b3b1b1b1b0b0b0b0b6b5PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcPd1;:?%EA5R:RA91diR?P8A1dhAC:P9Pfb4b7b8X2:12kCR;106>Rn/2C[^2:P2PeP\O2R\b3b1b1b1b0b0b0b0b6b5PGM9BPLPPPFPDPEPJPKPDPEPHP=PJP>P1PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcA1d<hP9Pfb4b7b8X2:122j^2:P5b3b1b1b1b0b0b0b0b6b5PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcA=:hgRJ=1diP9Pfb4b7b8X2:10j>/2k^2:P5b3b1b1b1b0b0b0b0b6b5M9APIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcPdPlP8A1d0hC:P9Pfb4b7b8X2:%7n\m^2:P^b3b1b1b1b0b0b0b0b6b5PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcPdP?P8A1dJAC:P9Pfb4b7b8X2:10n>/2C\;^2:P\b3b1b1b1b0b0b0b0b6b5P4M9BPNPOPFPDPEPMP3PDPEPHP=PMP>P1PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPc1;:@9=:<RM91d<P9Pfb4b7b8X2:102@R<,22^2:P5b3b1b1b1b0b0b0b0b6b5PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcA=:MgRg=1diP9Pfb4b7b8X2:10<>/2k^2:P5b3b1b1b1b0b0b0b0b6b5M9APIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcPdPlP8A1d0MC:P9Pfb4b7b8X2:106@R@#7\m^2:P^b3b1b1b1b0b0b0b0b6b5PIPQPBPRPSPWPXPVPYPUPZPTP[PVP]PUP_PTPaP`PbPcPdP?P8A1dgAC:P9Pfb4b7b8X2:10@>/2C\;^2:P\b3b1b1b1b0b0b0b0b6b5P6M9BPDPEPHP=P1P2E\CCCCCCW>WAP6P2O2n2001000000121000000W9W@P6P2O2n2001000000121000000W9W?P6P2O2n2001000000121000000W9W=WBW:X<7X;:P6P2O2W<X;:o"). Qed.

Lemma lvec_at_agree v b k lv : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PQM.LSZ * 2 ^ k <= 2 ^ 64 -> ag v 24 -> ag b (PQM.LSZ * 2 ^ k) ->
  PQM.lvec_at segs T3 T4 M v b k lv -> PQM.lvec_at segs T3 T4 M' v b k lv.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "h02T4h12T3h24__x1h31Hh42H0h52H1h62H2h72H3h87__arithh94__ffh:7__sat17h;7__sat18h<7__sat19h=7__sat20h>7__sat21h?8__varmaph@5__withA4cstrhB1ihC1qhD1rhE2HahF4__p1hG4__x2hH4__x3hI3Hn0hJ4__x4hK5cstr0hL4__x5hM4__x6hN1bhO1khP2lvhQ1vhR3AGBhS3AGVhT2DBhU1EhV2ELhW3HalhX2HbhY3Hb'hZ2Hkh[4Hlenh\2Hnh]3Hn1h^2Hvh_3Hv'h`2Hxha2P2hb2V0hc3V16hd2V8he2_Hhf3_H0hg1np%0p%1p&0p;1p;2p;4p;8p;3p;9p;6p;7p;<p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0p1001FR1p4p710p8P0P1p4p7210p8P0g001cR0p4p710R1p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R2p1005_p4p710p8P2P1p8P2p1006Ap4p710R2p8p1006]p606000p1007]p4p771111110p8P2p1008bp4p710p8g00EWk10=Tg00I=j1pTg009@j1JTg00WXj1PTg00X6j22Tg00;Hk408Tg01kIj8ETg00]Tj4VTg00<Hj23Tg00fLR2j15Tg00flR1j2?Tg00V7j3`Tg00=]R3j21Tg00gDj1NTg00gij3bTg00hZj29Tg00^Qj2WTg00_9j3XTg00i:j2eTg00?Zk10@Tg00i[j2CTg00j8j2kTg00=AR4j2;Tg00j_j2jTg00kFj2hTg00klj2gTg00DWk10VTg00GQk10UTg00Gok10TTg00W5j2\Tg00HZk20<Tg00>^k10STg00K0k20QTg00KRk20;Tg00Klk20PTg00?@j3aTg00LXk30NTg00M7k40MTg00lRk20KTg00<dj27Tg00_]l9rTg009ek10JTg00`ak30ITg00bNm901Tg00mRj2>Tg00mok60HTg00o4j4|Tg00B:j1RTg00BYk206Tg00Ckj2oTg00E7j3nTg00FUk10GTg00JEj4mTg00o[j2uTg010Gj3^Tg010jk10FTg011Hk20ETg011ij3lTg012Rj2yTg013;j3xTg013dk60DTg01lJk60BTg00cRj4vTP0k200Tg015Xk405Tg01ePk40:Tg00F7k20ATg00Mij7tTg0164k60LTg00NMk70?Tg00O1j8cTg00Ibk30OTg016Xm<0>Tg00CBk303Tg00G3k40RTg00UYR0f0R5'3p=0f2R6f1R7'7/35p=<g01iLR81275'>p=@g01jIR90005#5p=U1>85p=4f5R:f4R;f3R</761775CVp=I13061375'1p=L20095,?7p=HP:P;17<6P9P7P5g01mXR=H05H0:p=8g00A\R>f7S00f6R?'9;a0A`:;<1175,16'1'1p=F1175,16p=G20095p=61367/15p=s%55,>8p=D1975=a>0p=~A`:;<1175,16'1p>071;05p=KAa>50p=O1>67/75p=QAa>75p=B1375,16p=i20A>5p=]P6g00P<S01g00P[R8P8g00Q;R@P>P7g00OURAP5Cmg00Q[RBFtp=:P7Q01P8P8P@P5J0Lp=fP6Q01P8P8P@P7P5K0?p=dP<Q01P8P8P@P6P7P5Gcp>04P9P7P5P=H05p>09P;P<1767P5H0:p>02B0O>75p=AP:Q01P8P8P@P;P<P6Q01P8P8P@P>P7PAP5CmPBFtGcp=M20;>5p=Yg019;RAP>P1P2P4g019ZP:P;P<P6P7P5N<0>p=}1307/15p=_206>5p=ZB03>75:03>6p=[P>P6P7P5H0Rp==20<>5p=TP7Q01P8P8P@P5PBFtp={P?Q01P8P8P@P:P;P<Q01P8P8P@P6P7P5GcGcp=SB03>75p=zP>P7g01:<P5Cmp=wP;Q01P8P8P@P<P6P7Q01P8P8P@P5PBFtGcp>0CP?P:P;P<P6P7P5CvCvp=q&0=9S02Q02%0<S03g00A7S04#pS05#JS06#J#J#PR9Q04#JS07#PRBQ07#JS08#JS09#JR4#J#JS0:#PR2'2R15<;%0;S0;1@B;=<:1p,1MR=p,2M'RCQ00P9H08P=PCQ001@B?H08p,4segsRDp,2T3REp,2T4RFP=f9RGf8RHQ00P?GEP3PDP=f:S0<PGCVPDP=Q0<Q09#PRIPGQ00#URJ#4RKEIPDP=Q0<%P4R4PG12BHRL#4RMEIQ07#pS0=#p#PRN9LHH13JLPGP4P=PGPMPEP=PGPKO3PFP=PGPKPMO41H5HPDP=f;RM%57S0>#4RKP7PGE8[^BAGF3G3GPDPEPFPCPMQ0<PGPHGEP5PDP=f<RLPMCVPDP=f=RJPIPLQ0<#URO#4RPEIPDP=PJP4PL12BMRQ#4RREIALMMN13OQPLP4P=PLPRPEP=PLPPO3PFP=PLPPPRO4%6MRM,?5PDP=f>S0?PKP7PLE8[^BAGF3G3GP3PDP=Q0?PIPJ%5MRM#4RREIPDP=Q0?P4PJ12BLRP#4RQEIALLLNPJP4P=PJPQPEP=PJPRO3PFP=PJPRPQO41H5LPDP=f?RQPKP7PJE8[^BAGF9sMP3GPDPEPFPCPQQ0?PJPLGEP5PDP=f@RLPIPQ%6J#DEIPDP=fARJP4PL12BQRP#4RMEIALQQNQ0?#URRPLP4P=PLPMPEP=PL%4RRRO3PFP=PLPRPMO4%6QRQ,?5PDP=fBS0@PKP7PLE8[^BAGF7sP3GP3PDP=Q0@P4PJ12BLRP#4RMEIALLLN%5QRQ/3PPJP4P=PJPMPEP=PJ%4QRQO3PFP=PJPQPMO41H5LPDP=fCRMPKP7PJE8[^BAGF3GPDPEPFPCPMQ0@PJPLGEP5PDP=fDRLP4PMQ0@,@BEIALMMNQ0@#URJ12BMRQ'3PLP4P=PL%4QRQPEP=PL%4JRJO3PFP=PLPJPQO4%6MRM,?5PDP=fFS0APKP7PLE8[^BAGF3GP3ALLLN%5MRM12BLRQfERJP4P=PJ%4QRQPEP=PJ%4MRMO3PFP=PJPMPQO41H5LPDP=fGS0BPKP7PJE8[^BAGF3sPDPEPFPCQ0BQ0APJPLGEP5Q0AQ0A;LNQ0A#URJQ0B,2BRQfHRMP4P=PM%4QRQPEP=PM%4JRJO3PFP=PMPJPQO4Q0B#6RQ,?5PDP=fJS0CPKP7PME8[^BAGF3sP3%5QRQ12BMRJ'3fIS0DP4P=Q0D%4JRJPEP=Q0D%4QRQO3PFP=Q0DPQPJO41H5MPDP=fKS0EPKP7Q0DE8[^BAGFPDPEPFPCQ0EQ0CQ0DPMGEP5Q0D#UQ0C,2B'3fLRMP4P=PMQ0E,@BRJPEP=PMQ0C#6#DRQO3PFP=PMPQPJO4Q0E#6RJ,?5PDP=fNS0FPKP7PME8[^BAGFP3fMRQ/~4P=PQ1@BMRPPEP=PQ%DJRJO3PFP=PQPJPPO41H5MPDP=fORPPKP7PQE8[^BAJ07PDPEPFPCPPQ0FPQPMGEP51~P4P=fPRM1@BPRQPEP=PMQ0F#6#DRJO3PFP=PMPJPQO4%6PRP,?5PDP=fRS0GPKP7PME8[^BAJ07P3fQRQ1@BMRJ5`=PEP=PQ%DPRPO3PFP=PQPPPJO41H5MPDP=fSRJPKP7PQE8[^BA3GPDPEPFPCPJQ0GPQPMGEP5Q0G,@B9`=JPEP=fTRMQ0G#6#DRQO3PFP=PMPQ1@BJO4%6JRJ,?5PDP=fVS0HPKP7PME8[^BA3GP3PEP=fURQ%DJRJO3PFP=PQPJ1@BMO41H5MPDP=fWS0IPKP7PQE8[^BA'1PDPEPFPCQ0IQ0HPQPMGEP5PEP=Q0I%6Q#DO3PFP=fXRQQ0H#6#DQ0I,@BO4Q0I#6RM,?5PDP=fZS0JPKP7PQE8[^BA'1P3PFP=fYR3%DM1@BQO41H5QPDP=f[S0KPKP7P3E8[^BAPDPEPFPCQ0KQ0JP3PQGEP5PFP=Q0K%63#DQ0J,@BO4Q0K#6RQ,?5PDP=f^RMPKP7f\S0LE8[^BAQ0L%NQ%5Q#0AbM43%04S0Mf_R3/94#0[1WB2RQ%KBS0N%02%K1[[RJ%0BRPg00doRRAXB27UWER2%01\R^EPROf`S0O,WBQ0NfaS0P#0fbS0Q,2BS0R#K[[fcS0S=XB7VRXEPQ0S,2BRS#0\R^EPQ0S/e4%O4RT$0@S0TfdRU1CU419U45Q4'B[1kU4%K4S0UfeS0V/94RV#0S0W1;V4'1[Q0V/j41;40S0XffS0Y/94RW,;4?iW0[Q0Y/h4fgS0Z/C4#O\TQ0Z/g4fhRX/94/BX\T1CX4RYP>fiRZ/94R[P>PFPCO1R\p-0R]\>R^\>R_\>R`P5P6O1RaP_P5P<O1RbP^P5P;O1RcP]PEPCO1RdP_P5P?O1ReP^P5Q00O1RfP]g00R;S0[$0VRgQ0[$0=Rh%]7Ri&0U>Rj&0T>Rk1\>0S0\Q04-0<>Rl5:kS0]1fk<5dk&0S8RmQ0]H0420Qk@RnP5P6g00TYRog00U9Rp+0;20P56=aopdB0N>07H0MRpb9b?b@X2>XF]%05S0^/17%07S0_[^2>^F]P5fqS0`/3NQ0`Q0JO3b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bA+0KQ0L,2B#KPDPCP3PMCVPDPC173IS0aQ0L#6Ro#5Rq#4Rr,7MS0bCVS0cPDPC1734S0df]S0e,2BS0f#4Rs,7MS0gCVS0hQ0eQ0e;LNS0iQ0f,3qS0j1~M4S0kA`CMsS0lPEPCPMPrO3S0mPFPCPMPrPsO4S0nQ0e,H5S0oPDPCQ0OPK2097MS0pI02[^BAS0q'1S0r'1S0s'1S0t'1S0u'1S0v'1S0w'1S0x'1PDP=PCP3PMP=PCP3P9P3PIQ0I%NoS0y%0qRqQ0J9b34RoQ0MQ0O/94#0[RKPQPJP2POQ0P,WBRsQ0NQ0Q#0%KS[[RSAXBU7VRXEPRr12BU#0\R^EPRt1eU4RuQ0TQ0VQ0V/C4=Q4V'B[RVQ0V/k4RvQ0U%0WS0z1;W4'1[RWQ0Y/j4RwQ0XQ0Z/94S0{,;4Q0{;i0[RxQ0Z/h4Ry%OY\TRY1gX4Rz1B[Z\TR[1CZ4R{P>fjR|/94R}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjA:kllPnPpb9b?b@X2>1355^2>P5ftS0|O1S0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPj1\>IS0~,AlS101\>9R~,AlS115:kPnPpb9b?b@X2>175IS121759S13'3^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAM9rQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjPkQ0]PmQ0]H04PnPpb9b?b@X2>Q0^Q0_[^2>P5Q0|fpS14O2S15b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjPkQ111\>BQ0:$0J60I>S0:5:kS16PmPkQ10Q0:EMPnPpb9b?b@X2>Q13/31S17177IS18/31[^2>P5Q0|foS19O2S1:b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0GN901Q0cQ0xPDP=PCQ0aQ0bP=PCP3P9Q0aPIQ0IQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjQ109:klPnPpb9b?b@X2>Q12,35^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjQ10Q0~'AS0aQ115:kPnPpb9b?b@X2>Q12Q137<I^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAM9rQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjPkQ0]PmPkQ0\Q10EMPnPpb9b?b@X2>Q0^Q18#0[^2>Q15b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjPkQ16PmPkQ0aQ0:EMPnPpb9b?b@X2>Q17Q18?<I1[^2>Q1:b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0FN901Q0hQ0wPDP=PCQ0dQ0gP=PCP3P9Q0dPIQ0IQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPj1\>4S0I,AlS0d9:klPnPpb9b?b@X2>1754S0g,35^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjQ0dQ0~'AS0~Q115:kPnPpb9b?b@X2>Q0gQ137<I^2>Q0}b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAM9rQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjPkQ0]PmPkQ0\Q0dEMPnPpb9b?b@X2>Q0^1774S0d#0[^2>Q15b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0yPqPoPKPQPJP2POPsPSPrPtPuPVPvPWPwPxPyPYPzP[P{P>P}P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhPiPjPkQ16PmPkQ0~Q0:EMPnPpb9b?b@X2>Q17Q0d?<I1[^2>Q1:b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bAQ0CN901Q0iQ0vQ0AQ0jQ0uQ0@Q0kQ0tQ0?Q0lQ0sP=PCPMQ0f,>9Q0HQ0<J0HQ0mQ0rg01:cRiQ0nQ0qPiQ0oP<P7P5O2PDP=Q0OQ0>,>9Q0pI02%63Ri,?6%56R{%5iR[';RzP6P{%Y{PiP[%Y[E}P7C|PzQ0O#6Rz#N%5zR[#0%N;%5;Ri#0AbU43Q0MQ0W[PQPJP2POQ0Y,WBQ0NQ0Z#012BX#K[[AXBZ7VRXEP12BZS0W#0\R^EP1eZ4Q0T1C|4=Q4},B|[1k|4Q0UfkR}/94RU1;U4'_[1j}4Q0XflRY/94Ry,;4?iy0[1hY4fmRx/C4#O\T1gx4fnRw/94RW/Bw\T1Cw4S0pP>Q19/94S0>P>P\P`PaP_PbP^PcP]PdP_PeP^PfP]Q0[g00RgRv#R#RRV#RS0q#ZRu%ZVS0n206>vRv3[g00SFRV'o;ngPh&0G>Rt%];Rr7=6%]<RS?=;t7=7PjPkP>Plg00T2Q06#TRsCm,{kPmPkQ07#TRK9:ksPmPkQ0\Q0=#T5:kRs1fk?5dkPmQ04#PRo,\>,Al=:kKS0=H04FSPnPpb9b?b@X2>XG>XH>XJ>XF]1;5<13;6Q0;/1?A<<o;[[[^2>^G>^H>^J>^F]P5fwRq/3Nfv#UPq12BqQ0D#5Q0AQ0LQ0OO8b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIQ0O,2B9<{o1?<z%5<R{/;[RqP<P{%Y{PzP[%Y[E}P6C|PqQ0P#6Rq#N%5qR[#0%N:%5:#0Q0VQ0O7b4Q0MQ0z[PQPJP2POQ0Z,WBQ0N%0XQ0W#K[[AXB|7VRXEP12B|S0W#0\R^EP1e|4Q0T1C}4=Q4U,B}[1k}4Q0U1;y4,_y[1jY4Q0X19x4RU,;4?iU0[1hx4Q0p#O\T1gw4Q0>Q19'B\TQ19/C4S0>P>Q14/94S0pP>P\P`PaP_PbP^PcP]PdP_PeP^PfP]Q0[1zvu/oV,uv;ngS0ZPh%]6S0zA=S<t7=7S0VPjPkQ0=PmPk1fk:9dksS0=PmA^>~l/A~A^>~KR|5:kFSPnPpb9b?b@X2>XG>XH>XF]A<5o7Q03/1;S031>96Ro1>9<Rz7<9S0O[[^2>^G>^H>^F]P5fxS0A/3NQ0AQ0A,2BQ0C#5Q0BQ0PO6b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbI1>9{Q0P,2B,>97<9Q0S1>9i'7S0CQ0P-09;S0A1?;q1;i[R{P;Pi%YiPqP[%Y[E}P<C|S0DP{Q0Q#6R[#NS07%5[#0S06%N?S0r%5?#0S0mQ0YQ0P7b4S0YQ0MQ0{#0[S0MPQPJP2PO1WBXS0{Q0N%0ZQ0W#K[[S0NAXB}7VRXEPS0W12B}#0\R^EPS0P1e}4R}Q0T1CY4=Q4y,BY[Ry1kY4RYQ0U1;U4,_U[RU1jx4RxQ0X1;4W?iW0[RW1hw4RwQ0>#O\TR0Q19/g4RPQ0pQ14'B\TRRQ14/C4RZP>Q0`/94RXP>P\P`PaP_PbP^PcP]PdP_PeP^PfP]Q0[Q04$0F-0E>R[Q0q#RS0q#RS04#ZRq5l>Al>[u;[vQ05#P,y>=x>q,zv1y>4=x>vQ04#RS04#R#Z1zqu3[/oV'u'u;ngPh%]:S0`?=:t?=6tA=S:r7=7PjPkPkPkQ01P8P8P@Q0IQ0\'w,{kJ0DPmPkQ0IQ09#T5^>Q05#p#TR@'A,wlI0CS0IPmPkQ0\=:kKS09PmPkQ0\,w@,{kS01PmPkQ00,fk9dksPmPkQ0]PmPkQ0\1Al|R@EMFSFSPnPpb9b?b@X2>XG>XH>XJ>XL>XF]g01;?\TS0\AQ4:;,B7[%06%O:1_:HQ0;1>9?RT,7:S0]#0[[[[[^2>^G>^H>^J>^L>^F]P5fyRK/3NS0;PGPHPKQ0E#5RNfzR8Q0?PLQ0JQ0QfuO;b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIQ0DP{Q07Q06Q0rQ0mQ0YQ0MPQPJP2POQ0{Q0NQ0WQ0PP}PyPYPUPxPWPwP0PPPRPZP>PXP>P\P`PaP_PbP^PcP]PdP_PeP^PfP]Q0[A[quv1y>I=x>vQ04#Z9l>[Q0q#Z9l>[Q0n5[q3[/oV'u;ngPh%]??=<t?=6tQ0`9=r?7=7PjPkQ0IPmPk1A|~R|Q08#T9^>~Rr5:kPmPkQ01PmPk1fkH9dksPmPk1AlrQ0:5:kPmPk1A@~RrQ0:EMFSFSPnPpb9b?b@X2>XG>XH>XJ>XL>XM>XF]Q0\AQ4?:,B7[Q0O%O?1_?GA<;T1Q0]?<91[[[[[^2>^G>^H>^J>^L>^M>^F]P5Q0;PGPHPK12BKRBPNP8Q0?Q0BQ0JQ0QQ0|O<b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIP=PCQ0SQ0R,>9Q0CP9Q0KQ0DP{Q07Q06Q0rQ0mQ0YQ0MPQPJP2POQ0{Q0NQ0WQ0PP}PyPYPUPxPWPwP0PPPRPZP>PXP>P\P`PaP_PbP^PcP]PdP_PeP^PfP]Q0ZPhQ0VPjPkQ09PmPkQ0=PmA:kl@FSPnPpb9b?b@X2>XG>XH>XF]Q0_Q03176z,36[[^2>^G>^H>^F]P5Q0;PKPNP8PLQ0QO6b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIQ0DP{Q07Q06Q0rQ0mQ0YQ0MPQPJP2POQ0{Q0NQ0WQ0PP}PyPYPUPxPWPwP0PPPRPZP>PXP>P\P`PaP_PbP^PcP]PdP_PeP^PfP]PgPhQ0z?=7SPjPkQ05#T9^>~R~9:k|PmPkPr1Al~EMPnPpb9b?b@X2>XG>XH>1>97?<9o177o177z7<9[^2>^G>^H>P5PBPNP8Q0BO4b8b1b1b1b0b0b0b0bDbCb7b6b5b4b3b:b;b<b=b>bKbAbIM9rP6J0BPDPCQ0S%4iQ0AI02eb`b]bUW\XgACvFqFqFqFqPDPEPFPCP3PMQ0eQ0LGEebaWVWfP7P5O2n2001000000121000000W3WeP7P5O2n2001000000121000000W3WTP7P5O2n2001000000121000000W3WWP7P5O2n2001000000121000000W3W[P7P5O2n2001000000121000000W3WZP7P5O2n2001000000121000000W3WcP7P5O2n2001000000121000000W3WdP7P5O2n2001000000121000000W3WbP7P5O2n2001000000121000000W3WRWSWYWXW_W^WPXO>XN>XQ>P<P6P7P5O4WPXO>XN>XQ>o"). Qed.

(* [comment removed for export] *)
Lemma kstr_at_keep o x : 0 <= o -> o + 24 <= 2 ^ 64 -> ag (fst (vs_cells o x)) (snd (vs_cells o x)) -> dkr M M' o 24 ->
  (forall c n p, x = PM.VLong c n p -> dkr M M' p c) ->
  PQM.kstr_at segs T3 M o x -> PQM.kstr_at segs T3 M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "p'0h02T4h12T3h24__x1h31Hh47__arithh52H0h64__ffh78__varmaph85__with92H1h:2H2h;2H3h<2H4h=2H5h>7__sat17h?7__sat18h@7__sat19hA1qhB1rhC1ni001nhD1ci011chE1pi021phF2AGhG3DKBhH6__sat5hI6__sat6hJ2HahK2HnhL2_HhM1ohN1xhO2B0hP1DhQ2DBhR2DKhS2HchT2HehU2HohV3Ho'hW2W0hX3W16hY2W8i033cnti041si051vp%0p&0p;1p;2p;4p;3p;5p;6p;9p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0g001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R2p1005_p4p710p8P2P0p8P2p1006Ap4p710R2p8p1006]p606000p1007]p4p771111110p8P2p1008bp4p710p8g00I=j1TTg009@j19Tg00WXj1@Tg00<dj23Tg00X6j2|Tg00<Hj21Tg01@Uj2UTg00;Hj4ITg00@3j4ZTg01A^j3VTg00?@j3<Tg01nYj5YTg00V7j3;Tg00=]R2j20Tg00mRj2ETg01=Sj6`Tg01C[j1_Tg01DYj4FTg00^Qj2iTg00=Aj24Tg00_9j3hTg00DWj1gTg00EWj1fTg00F7j2eTg00GQj1dTg00Goj1cTg00HZj2bTg00K0k203Tg00KRj2aTg00Klk202Tg00LXk301Tg00M7k400Tg00W5j2HTg00_]l9STg00>^j1{Tg009ej1zTg00`aj3yTg01EUl9xTg00cRj4:Tg00]Tj4=Tg00gij2tTg00hZj2CTg00i:j2sTg00?Zj1rTg00i[j2WTg00j8j2qTg00j_j2pTg00kFj2vTg00klj2wTg00bNl9XTP1j3oTg01FXj3nTg00JEj4mTg00Mij7}Tg00Ibj3~Tg00O1j8lTg00UYR1f0R0'1p=6g00A\R3?o30p=RAn330p=Kf4R4f3R5f2R6f1R7P0CF'0p=B1470,06p=ug01oZR8,10p=M1167/00p=O1C70=<31p=N1070,06p=Jf5R9P41356P7C=/00p=2P4P5P6P7C=/00p=D1116/07/00p=k1067/00p=jP6g00P<R:g00P[R;P;g00Q;R<P3P7g00OUP0Cmg00Q[F}p=8A~370p=GP5P:P;P;P<P6P7P0Glp=A1C94=<31A;567/00'0p=511561178'0/00p=71467,05/00p=QP9P4P51367C=/00p=>P4P5P61370C=p=^P4P51367P0C=p=Pf7R8f6R:1394P5C=1116/07/00'0p=?11151467'0/00p=]1117/00p=LA;567/00p=\A<301p=[g01G5R=%67R>g00A7R?#T#9R@#9#9#@RA,36%9?RB#@RC%9B#9RD#9RE#9#9RF#@RG'|RH'1p,1MRIp,2M'RJ1U56RK#R%KKCIPIPJP4PACZAV670RK9<=8PIPJP7P5CZRL[^E3^C3^D3p,4segsRMp,2T3RNPIP:P9DYP2A;I8APNPIP8PAO3P=p-0ROP:%60RP%TB#T#9#@RB,10'0RQPMPIf8RR1EC0RSDBPMPIf:RT%@?RU,36RVPMPIPT%@DRDP7PMPIPT%@EREP0Au>76RW%T@#9#@R@%M67O6RX1N6CRYA;I06PNPIP0P6O33J3JRZE2E2DDn0110400021010030101100102'0PMPNPJPRP8DYP0f9R[=;IAPNPIPTPAO3P=POP[PQPMPIf;R\PSDBPMPIf=R]PVPMPIP]PDP7PMPIP]PEP0PZE2E2DDn0110400021010030101100102'0P2PNPIP\PAO3P=POPTPQPMPIf<R^PSDBPMPIf>R_PVPMPIP_PDP7PMPIP_PEP0PZE2E2DDn0110400021010030101100102PMPNPJP^P\DYP0PNPIP]PAO3P=POP]PQPMPIf?R`PSDBPMPIfARaPVPMPIPaPDP7PMPIPaPEP0PZE2E2DDn0110400021010030101100102A;J`APNPJP`PAO3RbP=POP_PQPMPJf@RcPSDBPMPJfBRdPVPMPJPdPDP7PMPJPdPEP0A;J06PNPJP0P6O35JY9JWXRXE2E2DDn0110400021010030101100102RW'0PIPJP`PAPTP9E`PbPWg01:cS00P=PIPJ1Uc0RW#R%KWCIA<=4KPL[^E3^C3^D3P=POP6PQPMPIfCRWPSDBPMPIfERbPVPMPIPbPDP7PMPIPbPEP0PZE2E2DDn0110400021010030101100102P=POP5PQPMPJfDRQPSDBPMPJfFRSPVPMPJPSPDP7PMPJPSPEP0PXE2E2DDn0110400021010030101100102]3]G]FP_PIPJ%_0,UaRX#R%KXCI%_4=<=KPL[^E3^C3^D3116BPMPIPW1EC6CF5k6P2%65RX115B'0PMPIPQ1EC5CF%64RV114BPMPJPb1EC4CF3jP0%69RZ119B'0PMPIfGRY1EC:CF%68Re118B'0PMPJfHRB1EC8RfCFP7PMPIPJPBPfPIPJPBPUPBPUP:1iCGRf141CRg%6G141H[[Rh%6CRig00doRjAhCG7UWJRG%6H\j^JiRjp,2T4PJO1RkPO\3Rl\3Rm\3RnP0PTO1RoPmP0P\O1RpPlP0P^O1RqPOPNPJO1RrPmP0P_O1RsPlP0P`O1RtPOg00R;Ru#gRv%fuRu1e37Rw%d3Rx%c3Ry1b3?R?;8?203y<R<P0P6g00TYRzg00U9R{'a20206=<z{dB01317H00R{b6b7b8X23S011100^23S02P0fRRzO1R|b4b1b1b1b0b0b0b0bHbIPfPhPGPjPkPnPoPmPpPlPqPOPrPmPsPlPtPOPvPuPwPx1H3U,G?R}=8y}P<P{b6b7b8X23130UR~/1~^23P|b4b1b1b1b0b0b0b0bHbIM9SPfPhPGPjPkPnPoPmPpPlPqPOPrPmPsPlPtPOPvPuPwPxPy1H31S03=8y?S04%{;R;Q04CAP<P{b6b7b8X23S05P>\P^23S06P0PzfPR>O2b4b1b1b1b0b0b0b0bHbIPfPhPGPjPkPnPoPmPpPlPqPOPrPmPsPlPtPOPvPuPwPxPy1H3A,G?Rt1H3C%zF5y3RF58yS07P;A8y}FCAP<P{b6b7b8X23130AR}/1HRs137U/1H[^23P0PzfORqO2b4b1b1b1b0b0b0b0bHbIP0M9xC:WOWKP7P0O2n2001000000121000000W3WGWFXC3P0O1PIPJ1UbKR|#R%K|CIAV:94=<=KPL[^E3^C3^D3PMPIPYP4PUPMPIPYPDP5PMPIPYPEP6PXP5P4P@P4P4P4PCPIP6P4PNPIP6P4O3E5C7CQE2E2E>P2PMPIPBP9PUD^PMPIPBPDP4PMPIPBPEP5PVP4P9P@P9P9P9PCPIP5P9PNPIP5P9O3E5C7CQE2E2PMPJfIR5P:PUPMPJP5PDP9PMPJP5PEP4PZP9P:P@P:P:P:PCPJP4P:PNPJP4P:O3E5C7CQE2E2E>P0PMPIfJR4P8PUD^PMPIfKRZPDP8PMPIPZPEP:PeP8PRP@PRPRPRPCPIP:PRPNPIP:PRO3E5C7CQE2E2P2PMPIfLRePDPRDPPMPIPePEP8PR14R[P@P[P[P[PCPIP8P[PNPIP8P[O3E5C7G?PMPJfMRVPTPUPMPJPVPDP[PMPJPVPEPRP[14[TP@PTPTPTPCPJPRPTPNPJPRPTO3E5C7G?E2E>P0PMPIfNRXPDPTDPPMPIPqPEPTP\14\^P@P^P^P^PCPIPTP^PNPIPTP^O3E5C7G?P2PMPIP>PEP\DPP^P^P]P@P]P]P]PCPIP\P]PNPIP\P]O3E5C7C]PMPJfQRTP_PUPMPJPTPDP]PMPJPTPEP^P]14]_P@P_P_P_PCPJP^P_PNPJP^P_O3E5C7G?E2E>P0PMPIPzPEP]DPP`P`PcP@PcPcPcPCPIP_PcPNPIP_PcO3E5C7C]P214ca,LcP@PaPaPaPCPIP`PaPNPIP`PaO3E5C7PMPJfUR`PdPUPMPJP`PDPaPMPJP`PEPcPa14adP@PdPdPdPCPJPcPdPNPJPcPdO3E5C7G?E2E>P014dW,LdP@PQPQPQPCPIPdPQPNPIPdPQO3E5C7P2%Mb9O@bPbPCPIPWPbPNPIPWPbO3E5PMPJfYRWPSPUPMPJPWPDPbPMPJPWPEPQPb14bSP@PSPSPSPCPJPQPSPNPJPQPSO3E5C7G?E2E>P0%MY9O@YPBPCPIPSPBPNPIPSPBO3E5P21N5CPIPYP5PNPIPYP5O3C\PMPJf]RSP4PUPMPJPSPDP5PMPJPSPEPBP51454P@P4P4P4PCPJPBP4PNPJPBP4O3E5C7G?E2E>P01NZCPIP4PePNPIP4PeO3C\P2A;IZVPNPIPZPVO3PMPJfaRZPXPUPMPJPZPDPVPMPJPZPEPePV14VXP@PXPXPXPCPJPePXPNPJPePXO3E5C7G?E2E>P0A;IVqPNPIPXP>O3PMPJfdRe13TURUC=PMPJ13eDS08P>C=S09PMPJ13eES0:PqC=S0;14>T,L>S0<%MT9O@TS0=1NTCS0>A;JqTS0?PNPJPqPTO3S0@'0S0A'0S0B'0S0C'0S0D'0S0E'0PMPIPJPePUPIPJPePAPePDPXPfPhPGPjfSRU/tCRN%6U1C`CRU#6\i[RifT/sCR@%[CRZ#r1W`C,EC/3U9<3`[RU1q`CR`fVR4/CCRB14BC'L\gRg1p4CR414C1fWRB/CCRQ,4C11Q1'0[RQ1vBCRBfXR1/WC#[\ZRd1w1CR11CWC=<3W\ZRZ1WWCRWP3fZRc/CCRCP3P2%6cR_f[,4cRcfoRz/1zPYf\#6R^f^,4SRSPkPnP0P:O1R:PmP0P8O1R8PlP0PRO1RRPOPrPmPoPlPpPOQ01Q02P0fzS02O1RLb4b1b1b1b0b0b0b0W=W<P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@PfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc13zDRK13zAS01'1PYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPx1H3DS0F,G?R|=8ytP<P{b6b7b8X23130DR~/1}^23PLb4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@M9SPfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc%6zPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOQ05Q06P0Q02fxO2S06b4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@PfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc11KHPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxPyQ07P;A8y|FCAP<P{b6b7b8X23137DS05/1H\s^23P0Q02fwO2S02b4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000121000000bBbAb;b:b9b5b3b>b?b@P5M9XQ09Q0EPMPIPJQ08P>PIPJPePAQ08PDPXPfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc11zKPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxA8y?|P<P{b6b7b8X23110~^23PLb4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@PfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc13KDS08Q01'1PYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxQ0F,G|R5=8ytP<P{b6b7b8X2313~D/1}^23PLb4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@M9SPfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc%6KPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxPyQ04P;Q03=8y|CAP<P{b6b7b8X23Q05#6\P^23Q06b4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@PfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_PcQ08/1HPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxPyQ07P;A8y5FCAP<P{b6b7b8X23Q05/3D/1H\s^23Q02b4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000121000000bBbAb;b:b9b5b3b>b?b@PbM9XQ0;Q0DPMPIPJQ0:PqPIPJPePAQ0:PDPXPfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc13zERX,1zPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPx1H3E,G?Rz98y?P<P{b6b7b8X23130ER?,10^23PLb4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@PfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc13XDRAQ01'1PYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxQ0F,GzRe=8ytP<P{b6b7b8X2313?D/1}^23PLb4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@M9SPfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc%6XPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxPyQ04P;Q03=8yzCAP<P{b6b7b8X23137ERE#6\P^23Q06b4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000120000000bBbAb;b:b9b5b3b>b?b@PfPhPGPjPNPiP@PUP`PgP4PQPBPdP1PZPWP3PCP3P2P_Pc11AHPYPkPnP:PmP8PlPRPOPrPmPoPlPpPOPvPuPwPxPyQ07P;A8yeFCAP<P{b6b7b8X2313ED/1H\s^23Q02b4b1b1b1b0b0b0b0X=SX<^P7P0O2n2001000000121000000bBbAb;b:b9b5b3b>b?b@PaM9XQ0<Q0CP]Q0=Q0BP[Q0>Q0AP9Q0?Q0@PIPJPqPTPVPTP>PqAVT>q,a=O4P7E`Q00C:C:C:C:C:C:C:WLWQP7P0O2n2001000000121000000W3WTP7P0O2n2001000000121000000W3WSP7P0O2n2001000000121000000W3WKP7P0O2n2001000000121000000W3WXP7P0O2n2001000000121000000W3WYP7P0O2n2001000000121000000W3WWP7P0O2n2001000000121000000W3WGWFXE3XC3XD3P6P7P0O3n0110501021110031103100102P\P[P0O3C:C:W3WLP7P0O2n2001000000121000000W5WPP7P0O2n2001000000121000000W5WGWRWFWVWUXN=XM3P7P0O2WNXM3o"). Qed.

(* [comment removed for export] *)
Lemma adaptor_at_frame oa ov st :
  0 <= oa -> oa + PQM.ASIZE <= 2 ^ 64 ->
  dkr M M' oa PQM.ASIZE -> ag oa 24 ->
  ag (fst (vs_cells (oa + PQM.AOFF_KEY) (PQM.a_key st))) (snd (vs_cells (oa + PQM.AOFF_KEY) (PQM.a_key st))) ->
  (forall c n p, PQM.a_key st = PM.VLong c n p -> dkr M M' p c) ->
  ag (fst (vs_cells (oa + PQM.AOFF_KB) (PQM.a_kb st))) (snd (vs_cells (oa + PQM.AOFF_KB) (PQM.a_kb st))) ->
  (forall c n p, PQM.a_kb st = PM.VLong c n p -> dkr M M' p c) ->
  ag (oa + PQM.AOFF_LV) 24 -> 0 <= PQM.a_lb st -> PQM.a_lb st + PQM.LSZ * 2 ^ PQM.a_lk st <= 2 ^ 64 ->
  ag (PQM.a_lb st) (PQM.LSZ * 2 ^ PQM.a_lk st) ->
  PQM.adaptor_at segs A T3 T4 vpa M oa ov st -> PQM.adaptor_at segs A T3 T4 vpa M' oa ov st.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpModelFacts ()) ["Agree"] "h04__x1h17__arithh24__ffh37__sat17h47__sat18h57__sat19h67__sat20h78__varmaph85__with91Hh:2Hah;1ch<1nh=2oah>2ovh?1ph@2sthA3AG0hB3AGBhC3AGKhD3AGLhE4AGLBhF1DhG2DKhH3DKBhI3DKKhJ2H0hK3H16hL2H8hM2HbhN3Hb'hO2HohP3Ho'hQ2KBhR2KShS2LVhT2_Hp%0p;1p;2p;4p;3p;9p;5p;8p;6p;;p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000Np4p710p8P0p1000ep4p710p8P0g001FR1p4p710p8P0P1p4p7210p8P0p1001cp4p710R0p8p1002Cp4p710p1002`p4p710p8p1003<p4p70p10048p4p710p8p1004Up6061000R2p1005_p4p710p8P2P0p8P2p1006Ap4p710R2p8p1006]p606000p1007]p4p771111110p8P2p1008bp4p710p8g009@j15Tg00WXj1ATg00X6j2JTg00@3j4aTg00I=j1]Tg00;Hj4KTg020Xj12Tg01@Uj2ZTP1j3WTg01FXj3STg01A^j3|Tg00?@j3QTg021Wj1BTg022Uj1ITg023Sj1GTg00mRj2^Tg024Ql9?Tg00]Tj47Tg00<dj20Tg025Uj1eTg00V7j3VTg01nYj5@Tg026Xj1UTg01kIj8MTg00=]R1j21Tg00^Qj2TTg00=Aj2RTg00_9j3dTg00DWj1{Tg00EWj1zTg00F7j2yTg00GQj1xTg00Goj1vTg00HZj2uTg00K0j2sTg00KRj2rTg00Klj2qTg00LXj3oTg00M7j4nTg00<Hj2;Tg00_]l9NTg00W5j2_Tg00>^j1mTg009ej1kTg00`aj3jTg00bNl9OTg01=Sj6iTg01YBl9`Tg027Vj8\Tg028cl;hTg00cRj4HTg00JEj4bTg00Mij7cTg00Ibj3wTg00O1j8[Tg00UYR2f0R0';p=4f2R3f1R4'0/;0p=:g02:1R5,00p=Cg02;3R6,00p=Pg02<4R7,00p=pg02=5,00p=Eg02>8R89V40p=>f7R9f6R:f5R;f4R<f3R=/07%I3%G4%U0GMp=3P;P<P=1036%B4D@/10p=<P;P<P=P3P4D@/10,1:,19p==P<P=P3P4C7/10p=DP<P=P31045P0D@p=LP;P<P=1035P4D@/10p=YP<P=P31046P0D@p=XP3g00P<R5g00P[R>P>g00Q;R?g00A\R@P4g00OURAP0Cbg00Q[RBFcp=61_@0p=FAw@40p=8P=P5P>P>P?P3P4P0G[p=lP;P5P>P>P?P<P=P3P5P>P>P?P@P4PAP0CbPBFcG[p=9P9P:P;P<10=7P3P4P0GMp=gP;P<P=1036P4D@/10p=f1140,13p=tg02?7S00Q00%43g00A7R6#5R7#AR9%57R7#5RB#5RA#5#5R5#ARC'JRD9:=8p,1MREp,2M'RFP<P8CaPEPFP;%]6#5#5#5R8#ARGCKPEPF%C:%2<'ZR<9W@@AS@@<CKg01G5R<f8RH#2A|340RI3QPEPFP4P=CaR=[^?@^<@^;@PEPF%PH%B:'ZR:9W@@AS@@:CKf:R:#B=Q<IP=[^?@^<@^;@PEPF%p:PGCKf9#I#4%I:g01iLR=%G:,J9'^;:DPEPFf;R:#I%G:,J9,^=CKp,4segsR=p,1AR:p,2T3RIp,2T4R<p,3vpaRHPEf>RJf=RKf<M9?P1P=PEf?RLPHC7P=PEg02@6RM,0L%e:RNP=PE%ELPJ1>ELPIPEPLPGO3P=PIPE%CL%2KP=PIPEPLPKP=PIP<PEPLPKPKPKG3E<G=DDDDP=P:PIP<PHPFf@ROPLPJM9?P0P=PEfARJPHC7P=PEfBRL/0MPNP=PE%ELPJ1>ELPIPEPLPGO3P=PIPE%CL%2OP=PIPEPLPOP=PIP<PEPLPOPOPOG3E<G=DDDDP1P=PEfCRO/0MPNC7P=PE%EOPL1>EOPIPEPOPGO3P=PIPE%CO%2JP=PIPEPOPJP=PIP<PEPOPJPJPJG3E<G=DDP=P:PIP<PHPFfDRPPOPLM9?P0P=PEfERL/0MPNC7P=PEfFRO#EPL1>EOPIPEPOPGO3P=PIPE%CO%2PP=PIPEPOPPP=PIP<PEPOPPPPPPG3E<G=DDP1P=PEfGRP#EPOC71>EPPIPEPPPGO3P=PIPE%CP%2LP=PIPEPPPLP=PIP<PEPPPLPLPLG3E<G=P=P:PIP<PHPFfHRQPPPOM9?P0P=PEfIRO#EPQC7fJRP,>EPIPEPPPGO3P=PIPE%CP%2QP=PIPEPPPQP=PIP<PEPPPQPQPQG3E<G=P1fKRQ,>EPIPEPQPGO3P=PIPEPQ%2ODLP=PIPE%PQ%BOP=PIP<PEPQPOPOPOG3G=P=P:PIP<PHPFfLRRPQPPM9?P0fMRP,>EPIPEfNRQPGO3P=PIPEPQ%2RDLP=PIPE%PQ%BRP=PIP<PEPQPRPRPRG3G=P1PIPEfORRPGO3P=PIPEPR%2PP=PIPEPRPPP=PIP<PEPRPPPPPPG3E<EYP=P:PIP<PHPFfPRSPRPQM9?P0PIPEfQRTPGO3P=PIPEfRRU%2SP=PIPEPUPSP=PIP<PEPUPSPSPSG3E<EYP1P=PIPEfSRV%2TDLP=PIPEPVPTP=PIP<PEPVPTPTPTG3E<P=P:PIP<PHPFfTRWPVPUM9?P0P=PIPEfURX%2VDLP=PIPEfVRYPWP=PIP<PEPYPWPWPWG3E<P1P=PIPEfWR1%BXDXP=PIP<PEP1PXPXPXG3P=P:PIP<PHPFfXRZP1PYM9?P0P=PIPEfYR[%B1DXP=PIP<PEfZR1PZPZPZG3P=PFf[RZPHC7S01P=PF%ABRB,0ZR\PNC7S02P=PF%AARA,0ZR]P1C7S03%58R8#5#AR^9VFZS04PIPFPZPGO3S05P=PIPF10ZGR_%2[S06D@S07P=PIPF%A8R8,0ZR`%B[S08D@S09P=PIP<PF%]7#5#5#5#AR7,0ZS0:%I[S0;%G[Ra%U[RbGMS0<'1S0='1S0>'1S0?'1S0@'1S0A'1P=PEPFPZPHPEPFPZPGPZPBPX1T9aRc1R29Rd%G1#4%GZ,J9,R2[[Re%49Rfg00doRgf\S0B#GRh=d94UW:Ri1J9h#4\g^:fRh1T9CRj%4C1R2D[\dRdAd9C4VgX:fRC%4D\g^:fRfg00R;Rg#{Rk%zgRg1y@4Rl%x@Rm%v@Rn1u@6R6;661sn?R?P0P3g00TYRog00U9Rp'r1q03=QopdAo@24CnRpb2b7b8X0@1;00^0@P0f`RoO1Rqb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPm%FBRr,86Rs%FGRt,86Ru56nP?Ppb2b7b8X0@100BRv100GRw';^0@Pqb1b3b4b5b6M9NPcPePiPhPjPdPCPfPkPgPlPmPn1_@2R2=6n6Rx%m>R>PxClP?Ppb2b7b8X0@%40Ry%44[^0@P0Pof]O2Rzb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmPn%F^,86R{%F9%k55j@R556nR9P>PnPsP5E9P?Ppb2b7b8X0@100^R|/;DR}104BR~/;D[^0@P0PoQ0BO2Rob1b3b4b5b6POM9OQ02Q0AP=PEPFP\PNPEPFPZPGP\PBPXPcPePiPhPjPdPCPfPkPgPlPmA6n6sP?Ppb2b7b8X0@1;0v^0@Pqb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPm18srR\=6nuP?Ppb2b7b8X0@A:vBw^0@Pqb1b3b4b5b6M9NPcPePiPhPjPdPCPfPkPgPlPmPnPxP>PnP2PsE9P?Ppb2b7b8X0@%4~\y^0@Pzb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmPnP9P>PnP\P5E9P?Ppb2b7b8X0@A:~BD\}^0@Pob1b3b4b5b6PLM9OQ03Q0@P=PEPFP]P1PEPFPZPGP]PBPXPcPePiPhPjPdPCPfPkPgPlPm%FA,86RX96n6P?Ppb2b7b8X0@100AR],;0^0@Pqb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPm18XrRr=6nuP?Ppb2b7b8X0@A:]Bw^0@Pqb1b3b4b5b6M9NPcPePiPhPjPdPCPfPkPgPlPmPnPxP>PnP2PXE9P?Ppb2b7b8X0@104ARA#4\y^0@Pzb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmPnP9P>PnPrP5E9P?Ppb2b7b8X0@A:ABD\}^0@Pob1b3b4b5b6PJM9OQ04Q0?PEPFPZP^PYPKEiQ05Q0>g01:cQ07Q0=P_Q06PcPePiPhPjPdPCPfPkPgPlPmPnPxP>PnP2PuE9P?Ppb2b7b8X0@104GRK#4\y^0@Pzb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmPnP9P>Pn18utRJP5E9P?Ppb2b7b8X0@A:KGD\}^0@Pob1b3b4b5b6PWPEPFPZP^P_PGPYPcPePiPhPjPdPCPfPkPgPlPmA6n6uP?Ppb2b7b8X0@1;0w^0@Pqb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmA6nJ{P?Ppb2b7b8X0@A:wG|^0@Pqb1b3b4b5b6M9`PVP;G\Q09Q0<P`Q08PcPePiPhPjPdPCPfPkPgPlPmPnPxP>PnP2%F8,86R;E9P?Ppb2b7b8X0@1048RV#4\y^0@Pzb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmPnP9P>Pn18;tRwP5E9P?Ppb2b7b8X0@A:VGD\}^0@Pob1b3b4b5b6PUPEPFPZP^P`PGPYPcPePiPhPjPdPCPfPkPgPlPmA6n6;P?Ppb2b7b8X0@1008R8,;0^0@Pqb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmA6nw{P?Ppb2b7b8X0@A:8G|^0@Pqb1b3b4b5b6M9`PTP4G\Q0:Q0;PaPbPcPePiPhPjPdPCPfPkPgPlPmPnPxP>PnP2%F7,86R6E9P?Ppb2b7b8X0@1047R7#4\y^0@Pzb1b3b4b5b6PcPePiPhPjPdPCPfPkPgPlPmPnP9P>Pn186tP5E9P?Ppb2b7b8X0@A:7GD\}^0@Pob1b3b4b5b6PRPQPSPPP0M;hCHCHCHCHCHCHCHQ01P=PF10ZMPNC7P=PF%EZP11>FZQ05P=PIPF%CZQ06P=PIPFPZQ08P=PIP<PFPZQ0;PaPbGgEfG=DD3teP=P:PIP<PHPFPZP1P[M9?eWSWQP4P0O2n2001000000121000000W9WRP4P0O2n2001000000121000000W9WTP4P0O2n2001000000121000000W9WFP4P0O2n2001000000121000000W9WKP4P0O2n2001000000121000000W9WLP4P0O2n2001000000121000000W9WJP4P0O2n2001000000121000000W9WEWNWMWDWHWBWIWCWAWGWPWOW@X>@X=@P3P4P0O3W@X>@X=@o"). Qed.

End Agree.
End PQMF.

End PnMpModelFacts.
Module PnVis.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQV.

(* [comment removed for export] *)
Fixpoint ndig_f (f : nat) (v : Z) : Z := match f with O => 1 | S f' => if Z.ltb v 10 then 1 else 1 + ndig_f f' (v / 10) end.
Definition ndig (v : Z) : Z := ndig_f 20 v.
(* [comment removed for export] *)
Definition b64len (n : Z) : Z := (4 * n + 2) / 3.
(* [comment removed for export] *)
Definition sval (v : Z) : Z := if Z.ltb v (2 ^ 63) then v else v - 2 ^ 64.
Definition VIS_H : Z := 3.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AQ : pq_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation adaptor_at := (PQM.adaptor_at segs A T3 T4 (qa_vp_adaptor AQ)).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).

(* [comment removed for export] *)
Definition view_ok (M : word -> option byte) (sp oa : Z) (LBX : list (Z * Z)) (p d n : Z) : Prop :=
  L5.u64_at segs M p d /\ L5.u64_at segs M (p + 8) n /\ 0 <= n < 2 ^ 26 /\ L5.defined M d n
  /\ (n = 0 \/ PGS.in_blk LBX d n \/ (sp <= d /\ d + n <= oa /\ 4096 <= d)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vis_spec (pc : Z)
           (args : bvmap 5 word -> (word -> option byte) -> Z -> Z -> list (Z * Z) -> Prop)
           (pre : bvmap 5 word -> (word -> option byte) -> PQM.ast -> Prop)
           (step : bvmap 5 word -> (word -> option byte) -> PQM.ast -> PQM.ast -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r oa ov : Z) (st : PQM.ast),
    hi_heap HI (PQM.aown st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r VIS_H ->
    getr R 10%bv = Z_to_bv 64 oa -> args R M sp oa LBX ->
    sp <= oa -> oa + PQM.ASIZE <= hl_sptop L -> oa mod 8 = 0 -> sp <= ov -> ov + 8 <= hl_sptop L -> oa + PQM.ASIZE <= ov -> ov mod 8 = 0 ->
    adaptor_at M oa ov st -> PQM.adaptor_ok st -> PMSP.visitor_at segs A M ov -> pre R M st ->
    PMST.base_ok segs A M -> PMSP.credit_le (PQM.pot_adaptor L st) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (st' : PQM.ast) (cr' : credit),
        regs_preserved R R' ->
        adaptor_at M' oa ov st' -> PQM.adaptor_ok st' -> step R M st st' ->
        L5C.hpres L LBX sp (pm_scr VIS_H) (PQM.adaptor_W oa) M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_adaptor L st) (PQM.pot_adaptor L st') ->
        model_but_vm model model' -> hi_heap HI (PQM.aown st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition step_push (st st' : PQM.ast) : Prop := PQM.nlv st' = PQM.nlv st + 1 /\ PQM.kbsize st' <= PQM.kbsize st + 2.
Definition step_pop (st st' : PQM.ast) : Prop := PQM.nlv st' = PQM.nlv st - 1 /\ PQM.kbsize st' <= PQM.kbsize st + 2.
Definition step_val (d : Z) (st st' : PQM.ast) : Prop := PQM.nlv st' = PQM.nlv st /\ PQM.kbsize st' <= PQM.kbsize st + d.

(* [comment removed for export] *)
Definition no_args (R : bvmap 5 word) (M : word -> option byte) (sp oa : Z) (LBX : list (Z * Z)) : Prop := True.
(* [comment removed for export] *)
Definition pre_push (R : bvmap 5 word) (M : word -> option byte) (st : PQM.ast) : Prop :=
  PQM.nlv st <= PQM.MAX_DEPTH /\ PQM.kbsize st + 2 <= PQM.SMB.
(* [comment removed for export] *)
Definition pre_pop (R : bvmap 5 word) (M : word -> option byte) (st : PQM.ast) : Prop :=
  2 <= PQM.nlv st /\ PQM.kbsize st + 2 <= PQM.SMB.
(* [comment removed for export] *)
Definition pre_val (d : Z) (R : bvmap 5 word) (M : word -> option byte) (st : PQM.ast) : Prop := PQM.kbsize st + d <= PQM.SMB.
Definition d_u64 (R : bvmap 5 word) : Z := ndig (bv_unsigned (getr R 11%bv)) + 2.
Definition d_i64 (R : bvmap 5 word) : Z := ndig (Z.abs (sval (bv_unsigned (getr R 11%bv)))) + 3.
Definition d_double : Z := WD.WD_MAX + 2.
Definition d_null : Z := 6.
Definition d_bool : Z := 7.
(* [comment removed for export] *)
Definition view_len (R : bvmap 5 word) (M : word -> option byte) (n : Z) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ L5.u64_at segs M (p + 8) n /\ 0 <= n < 2 ^ 26.   (* [comment removed for export] *)
Definition args_view (R : bvmap 5 word) (M : word -> option byte) (sp oa : Z) (LBX : list (Z * Z)) : Prop :=
  exists p d n, getr R 11%bv = Z_to_bv 64 p /\ sp <= p /\ p + 16 <= oa /\ view_ok M sp oa LBX p d n.
Definition args_bstr_tag (R : bvmap 5 word) (M : word -> option byte) (sp oa : Z) (LBX : list (Z * Z)) : Prop :=
  args_view R M sp oa LBX /\ getr R 12%bv = Z_to_bv 64 0.
Definition args_bool (R : bvmap 5 word) (M : word -> option byte) (sp oa : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 11%bv = Z_to_bv 64 0 \/ getr R 11%bv = Z_to_bv 64 1.
Definition pre_str (R : bvmap 5 word) (M : word -> option byte) (st : PQM.ast) : Prop :=
  exists n, view_len R M n /\ PQM.kbsize st + n + 4 <= PQM.SMB.
Definition step_str (R : bvmap 5 word) (M : word -> option byte) (st st' : PQM.ast) : Prop :=
  exists n, view_len R M n /\ step_val (n + 4) st st'.
Definition pre_bstr (R : bvmap 5 word) (M : word -> option byte) (st : PQM.ast) : Prop :=
  exists n, view_len R M n /\ PQM.kbsize st + b64len n + 4 <= PQM.SMB /\ b64len n + 4 <= PQM.SMK.
Definition step_bstr (R : bvmap 5 word) (M : word -> option byte) (st st' : PQM.ast) : Prop :=
  exists n, view_len R M n /\ step_val (b64len n + 4) st st'.

(* [comment removed for export] *)
Definition v_begin_array_spec : Prop :=
  vis_spec (qa_v_begin_array AQ) no_args pre_push (fun _ _ => step_push).
Definition v_begin_object_spec : Prop :=
  vis_spec (qa_v_begin_object AQ) no_args pre_push (fun _ _ => step_push).
Definition v_end_array_spec : Prop :=
  vis_spec (qa_v_end_array AQ) no_args pre_pop (fun _ _ => step_pop).
Definition v_end_object_spec : Prop :=
  vis_spec (qa_v_end_object AQ) no_args pre_pop (fun _ _ => step_pop).
Definition v_uint64_spec : Prop :=
  vis_spec (qa_v_uint64 AQ) no_args (fun R M => pre_val (d_u64 R) R M) (fun R _ => step_val (d_u64 R)).
Definition v_int64_spec : Prop :=
  vis_spec (qa_v_int64 AQ) no_args (fun R M => pre_val (d_i64 R) R M) (fun R _ => step_val (d_i64 R)).
Definition v_double_spec : Prop :=
  vis_spec (qa_v_double AQ) no_args (pre_val d_double) (fun _ _ => step_val d_double).
Definition v_null_spec : Prop :=
  vis_spec (qa_v_null AQ) no_args (pre_val d_null) (fun _ _ => step_val d_null).
Definition v_bool_spec : Prop :=
  vis_spec (qa_v_bool AQ) args_bool (pre_val d_bool) (fun _ _ => step_val d_bool).
Definition v_string_spec : Prop :=
  vis_spec (qa_v_string AQ) args_view pre_str step_str.
Definition v_bstr_tag_spec : Prop :=
  vis_spec (qa_v_bstr_tag AQ) args_bstr_tag pre_bstr step_bstr.
Definition v_bstr_raw_spec : Prop :=
  vis_spec (qa_v_bstr_raw AQ) args_view pre_bstr step_bstr.
Definition v_flush_spec : Prop :=
  vis_spec (qa_v_flush AQ) no_args (fun _ _ _ => True) (fun _ _ => step_val 0).

(* [comment removed for export] *)
Record vis_ok : Prop := VISOK {
  vo_begin_array : v_begin_array_spec; vo_begin_object : v_begin_object_spec;
  vo_end_array : v_end_array_spec; vo_end_object : v_end_object_spec;
  vo_uint64 : v_uint64_spec; vo_int64 : v_int64_spec; vo_double : v_double_spec;
  vo_null : v_null_spec; vo_bool : v_bool_spec; vo_string : v_string_spec;
  vo_bstr_tag : v_bstr_tag_spec; vo_bstr_raw : v_bstr_raw_spec; vo_flush : v_flush_spec }.

End Specs.
End PQV.

End PnVis.
Module PnQRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mstack_shape (stk : list PQM.mstate) : Prop :=
  (1 <= length stk)%nat /\ Z.of_nat (length stk) <= PQM.MAX_DEPTH + 1
  /\ PQM.mode_bottom (PQM.ms_mode (nth 0 stk PQM.ms_root))
  /\ (forall i, (1 <= i < length stk)%nat -> PQM.mode_cont (PQM.ms_mode (nth i stk PQM.ms_root)))
  /\ (forall i, (i < length stk)%nat -> PQM.mstate_ok (nth i stk PQM.ms_root)).
(* [comment removed for export] *)
Definition minv_d (d : Z) (s : PQM.mpst) : Prop :=
  PQM.p_more s = 1 /\ PQM.p_done s = 0 /\ PQM.p_depth s = Z.of_nat (length (PQM.p_stk s)) - 1 + d /\ mstack_shape (PQM.p_stk s).
Definition minv (s : PQM.mpst) : Prop := minv_d 0 s.
Definition mmu (s : PQM.mpst) (sm : PM.strm) : Z := 4096 * PM.unread (PQM.p_src s) sm + 2 * Z.of_nat (length (PQM.p_stk s)).

(* [comment removed for export] *)
Definition mpush1 (s s' : PQM.mpst) : Prop :=
  exists c, PQM.p_stk s' = PQM.p_stk s ++ [c] /\ PQM.mstate_ok c /\ PQM.ms_idx c = 0 /\ (PQM.ms_mode c = 2 \/ PQM.ms_mode c = 3).
Definition mpush_rel (s s' : PQM.mpst) : Prop := PQM.p_stk s' = PQM.p_stk s \/ mpush1 s s'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pot_callM (L : heap_layout) (n : Z) : credit :=
  PM.credit_add (PM.credit_add (PM.cost1 L (n + 16)) (PM.cost1 L (n + 32)))
    (PM.credit_add (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.credit_add (PM.cost1 L PQM.PSZ) (PM.cost1 L PQM.LSZ)))
       (PM.credit_add
          (PQM.pot_run L
             (PQM.MPST 1 0 0 (PM.SRC 0 0 0) (PM.VShort 0) 0 PQV8.V8Null 0 0 0 [])
             (PQM.AST [] 0 0 (PM.VShort 0) 0 (PM.VShort 0) 0))
          PQM.TSRES)).

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AQ : pq_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation mparser_at := (PQM.mparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation adaptor_at := (PQM.adaptor_at segs A T3 T4 (qa_vp_adaptor AQ)).
Abbreviation err_ok := (PQST.err_ok segs A AQ).
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).

(* [comment removed for export] *)
Definition o_p (fb : Z) : Z := PMSP.o_p A fb.
Definition o_a (fb : Z) : Z := o_p fb + qa_off_a AQ.
Definition o_v (fb : Z) : Z := PMSP.o_v A fb.
Definition o_is (fb : Z) : Z := PMSP.o_is A fb.
Definition o_ec (fb : Z) : Z := PMSP.o_ec A fb.
Definition o_src (fb : Z) : Z := o_p fb + PQM.OFF_SRC.
Definition o_tb (fb : Z) : Z := o_p fb + PQM.OFF_TB.
Definition o_bb (fb : Z) : Z := o_p fb + PQM.OFF_BB.
Definition o_stk (fb : Z) : Z := o_p fb + PQM.OFF_STK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition make_ec_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o v sp r : Z) (b : bool),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 v -> 1 <= v <= 64 ->
    sp <= o -> o + 16 <= hl_sptop L -> o mod 8 = 0 -> L5.defined M o 16 ->
    PMST.base_ok segs A M -> err_ok M b ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> PMSP.ec_at segs M' o v (pa_errcat_obj A) -> err_ok M' true ->
        L5C.hpres L LB sp (pm_scr 1) ((o, 16) :: (if b then [] else PMSP.err_W A)) M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (pa_make_ec A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mrun_pre (M : word -> option byte) (fb : Z) (s : PQM.mpst) (st : PQM.ast) (str : PM.vstr) (sm : PM.strm) (e : bool)
           (n : Z) : Prop :=
  mparser_at M (o_p fb) (o_is fb) s /\ adaptor_at M (o_a fb) (o_v fb) st /\ iss_at M (o_is fb) str sm
  /\ PMSP.visitor_at segs A M (o_v fb) /\ L5.u64_at segs M (o_p fb + qa_off_vref AQ) (o_a fb)
  /\ PMST.base_ok segs A M /\ err_ok M e /\ PQM.mgrow_ok s /\ PQM.adaptor_ok st /\ PQM.cpl s st /\ PQM.acct n s st sm.
Definition W_mrun (fb : Z) : list L5.range :=
  [(o_p fb + 8, 8)] ++ PGS.W_srcfG (o_src fb) (o_is fb) ++ [(o_tb fb, 24); (o_bb fb, 24); (o_stk fb, 24); (o_ec fb, 16)]
  ++ PMSP.err_W A ++ PQM.adaptor_W (o_a fb).
Definition mown (s : PQM.mpst) (st : PQM.ast) : list (Z * Z) := PQM.mparser_own s ++ PQM.aown st.

Definition mprog := bvmap 5 word -> (word -> option byte) -> PQM.mpst -> PQM.mpst -> PQM.ast -> PQM.ast -> PM.strm -> PM.strm -> Prop.
Definition mrun_post_d (d : Z) (prog : mprog) (R' : bvmap 5 word) (M' : word -> option byte) (fb : Z) (s s' : PQM.mpst)
           (st st' : PQM.ast) (str : PM.vstr) (sm sm' : PM.strm) (e e' : bool) (cat n : Z) : Prop :=
  mrun_pre M' fb s' st' str sm' e' n /\ PMSP.src_step (PQM.p_src s) (PQM.p_src s') sm sm' /\ (e = true -> e' = true)
  /\ (   (exists v, 1 <= v <= 64 /\ PMSP.ec_at segs M' (o_ec fb) v (pa_errcat_obj A) /\ PQM.p_more s' = 0 /\ e' = true)
      \/ (PMSP.ec_at segs M' (o_ec fb) 0 cat /\ minv_d d s' /\ prog R' M' s s' st st' sm sm')).

(* [comment removed for export] *)
Definition mrun_spec_d (pc h d : Z) (args : bvmap 5 word -> Z -> PQM.mpst -> PQM.ast -> PM.strm -> Z -> Prop) (prog : mprog) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (s : PQM.mpst) (st : PQM.ast) (str : PM.vstr) (sm : PM.strm) (e : bool),
    hi_heap HI (mown s st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    args R fb s st sm n ->
    mrun_pre M fb s st str sm e n -> incl (PM.vs_own str) LBX -> minv_d d s -> PMSP.ec_at segs M (o_ec fb) 0 cat ->
    PMSP.credit_le (PM.credit_add (PQM.pot_run L s st) PQM.TSRES) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PQM.mpst) (st' : PQM.ast)
            (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        mrun_post_d d prog R' M' fb s s' st st' str sm sm' e e' cat n ->
        L5C.hpres L LBX sp (pm_scr h) (W_mrun fb) M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_run L s st) (PQM.pot_run L s' st') ->
        model_but_vm model model' -> hi_heap HI (mown s' st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Definition mrun_spec (pc h : Z) (args : bvmap 5 word -> Z -> PQM.mpst -> PQM.ast -> PM.strm -> Z -> Prop) (prog : mprog) : Prop :=
  mrun_spec_d pc h 0 args prog.

(* [comment removed for export] *)
Definition margs3 (R : bvmap 5 word) (fb : Z) (_ : PQM.mpst) (_ : PQM.ast) (_ : PM.strm) (_ : Z) : Prop :=   (* [comment removed for export] *)
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_a fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb).
(* [comment removed for export] *)
Definition ba_type (t : Z) : Prop := (144 <= t <= 159) \/ t = 220 \/ t = 221.
Definition bo_type (t : Z) : Prop := (128 <= t <= 143) \/ t = 222 \/ t = 223.
Definition margs_begin (P : Z -> Prop) (R : bvmap 5 word) (fb : Z) (s : PQM.mpst) (st : PQM.ast) (sm : PM.strm) (n : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 11%bv = Z_to_bv 64 (o_a fb) /\ getr R 13%bv = Z_to_bv 64 (o_ec fb)
  /\ (exists t, P t /\ getr R 12%bv = Z_to_bv 64 t) /\ PQM.acct_d 4 n s st sm.
(* [comment removed for export] *)
Definition gs_type (t : Z) : Prop := (128 <= t <= 159) \/ (196 <= t <= 201) \/ (212 <= t <= 223).
Definition margs_gs (R : bvmap 5 word) (fb : Z) (_ : PQM.mpst) (_ : PQM.ast) (_ : PM.strm) (_ : Z) : Prop :=
  getr R 10%bv = Z_to_bv 64 (o_p fb) /\ getr R 12%bv = Z_to_bv 64 (o_ec fb) /\ exists t, gs_type t /\ getr R 11%bv = Z_to_bv 64 t.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mprog_item : mprog := fun R' M' s s' st st' sm sm' =>
  mpush_rel s s' /\ PM.unread (PQM.p_src s') sm' < PM.unread (PQM.p_src s) sm.
(* [comment removed for export] *)
Definition mprog_push : mprog := fun R' M' s s' st st' sm sm' =>
  mpush1 s s' /\ PM.unread (PQM.p_src s') sm' <= PM.unread (PQM.p_src s) sm.
(* [comment removed for export] *)
Definition mprog_len : mprog := fun R' M' s s' st st' sm sm' =>
  PQM.p_stk s' = PQM.p_stk s /\ st' = st /\ PM.unread (PQM.p_src s') sm' <= PM.unread (PQM.p_src s) sm
  /\ exists len, 0 <= len < 2 ^ 64 /\ getr R' 10%bv = Z_to_bv 64 len.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_size_spec : Prop := forall d, 0 <= d <= 1 -> mrun_spec_d (qa_get_size AQ) 5 d margs_gs mprog_len.
Definition begin_array_spec : Prop := mrun_spec (qa_begin_array AQ) 6 (margs_begin ba_type) mprog_push.
Definition begin_object_spec : Prop := mrun_spec (qa_begin_object AQ) 6 (margs_begin bo_type) mprog_push.
Definition read_item_spec : Prop := mrun_spec (qa_read_item AQ) 7 margs3 mprog_item.

(* [comment removed for export] *)
Definition mpst_reset (s : PQM.mpst) : PQM.mpst :=
  PQM.MPST 1 0 0 (PQM.p_src s)
           (match PQM.p_tb s with PM.VShort _ => PM.VShort 0 | PM.VLong c _ p => PM.VLong c 0 p end) (PQM.p_tg s)
           (PQV8.v8_clear (PQM.p_bb s)) (PQM.p_bg s) (PQM.p_sb s) (PQM.p_sk s) [PQM.ms_root].
Definition reset_W (fb : Z) : list L5.range := [(o_p fb + 8, 8); (o_tb fb, 24); (o_bb fb, 24); (o_stk fb, 24)].
Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PQM.mpst),
    hi_heap HI (PQM.mparser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> mparser_at M (o_p fb) (o_is fb) s ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> mparser_at M' (o_p fb) (o_is fb) (mpst_reset s) ->
        (* [comment removed for export] *)
        L5C.hpres L LBX sp (pm_scr 1) (reset_W fb) M M' ->
        hi_heap HI (PQM.mparser_own s ++ LBX) cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@cfg fx' R' r M' model) K) ->
    srealizes segs SCFG (@cfg fx R (qa_reset AQ) M model) K.

(* [comment removed for export] *)
Definition mrun_fin (M : word -> option byte) (fb : Z) (s : PQM.mpst) (st : PQM.ast) (str : PM.vstr) (sm : PM.strm) (e : bool) : Prop :=
  mparser_at M (o_p fb) (o_is fb) s /\ adaptor_at M (o_a fb) (o_v fb) st /\ iss_at M (o_is fb) str sm
  /\ PMSP.visitor_at segs A M (o_v fb) /\ L5.u64_at segs M (o_p fb + qa_off_vref AQ) (o_a fb)
  /\ PMST.base_ok segs A M /\ err_ok M e /\ PQM.mgrow_ok s /\ PQM.adaptor_ok st.
Definition parse_post (M' : word -> option byte) (fb : Z) (s s' : PQM.mpst) (st' : PQM.ast) (str : PM.vstr) (sm sm' : PM.strm)
           (e e' : bool) (n : Z) : Prop :=
  mrun_fin M' fb s' st' str sm' e' /\ PMSP.src_step (PQM.p_src s) (PQM.p_src s') sm sm' /\ (e = true -> e' = true)
  /\ L5.defined M' (o_ec fb) 16.
Definition parse_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat n : Z) (s : PQM.mpst) (st : PQM.ast) (str : PM.vstr) (sm : PM.strm) (e : bool),
    hi_heap HI (mown s st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 8 -> frame_ok sp fb ->
    margs3 R fb s st sm n ->
    mrun_pre M fb s st str sm e n -> incl (PM.vs_own str) LBX -> minv s -> PMSP.ec_at segs M (o_ec fb) 0 cat ->
    PMSP.credit_le (PM.credit_add (PQM.pot_run L s st) PQM.TSRES) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PQM.mpst) (st' : PQM.ast)
            (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        parse_post M' fb s s' st' str sm sm' e e' n ->
        L5C.hpres L LBX sp (pm_scr 8) (W_mrun fb) M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_run L s st) PMSP.cr0 ->
        model_but_vm model model' -> hi_heap HI (mown s' st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (qa_parse AQ) M model) K.

(* [comment removed for export] *)
Definition src_layer_ok : Prop :=
  PGS.src_read_specG segs A L HI /\ PGS.fill_buffer_specG segs A L HI
  /\ PQV8.read_span_v_specG segs A L HI (qa_read_span_v AQ) /\ PQV8.srd_read_v_specG segs A L HI (qa_srd_read_v AQ)
  /\ PQV8.vu8_resize_spec segs A L HI (qa_vu8_resize AQ) /\ PQV8.vu8_append_spec segs A L HI (qa_vu8_append AQ).

End Specs.
End PQR.

End PnQRun.
Module PnVisN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNV.
Import NEM.

(* [comment removed for export] *)
Fixpoint ndig_f (f : nat) (v : Z) : Z := match f with O => 1 | S f' => if Z.ltb v 10 then 1 else 1 + ndig_f f' (v / 10) end.
Definition ndig (v : Z) : Z := ndig_f 20 v.
Definition b64len (n : Z) : Z := (4 * n + 2) / 3.
Definition sval (v : Z) : Z := if Z.ltb v (2 ^ 63) then v else v - 2 ^ 64.
Definition VIS_H : Z := 8.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AQ : pq_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
(* [comment removed for export] *)

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation ae_at := (NEM.ae_at segs A E L T3 T4 (qa_vp_adaptor AQ)).
Abbreviation ec_state := (NEM.ec_state segs A).
Abbreviation err_ok := (PQST.err_ok segs A AQ).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition view_ok (M : word -> option byte) (sp oa : Z) (LBX : list (Z * Z)) (p d n : Z) : Prop :=
  L5.u64_at segs M p d /\ L5.u64_at segs M (p + 8) n /\ 0 <= n < 2 ^ 29 /\ L5.defined M d n   (* [comment removed for export] *)
  /\ (n = 0 \/ PGS.in_blk LBX d n \/ (sp <= d /\ d + n <= oa /\ 4096 <= d))
  /\ 0 <= d /\ d + n <= 2 ^ 47.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vis_spec (pc : Z)
           (args : bvmap 5 word -> (word -> option byte) -> Z -> Z -> Z -> list (Z * Z) -> Prop)
           (pre : bvmap 5 word -> (word -> option byte) -> aest -> Prop)
           (step : bvmap 5 word -> (word -> option byte) -> aest -> aest -> bool -> bool -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r oa ov osk oec cat : Z) (st : aest) (b e : bool),
    hi_heap HI (aeown st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r VIS_H ->
    getr R 10%bv = Z_to_bv 64 oa -> args R M sp oa oec LBX ->
    sp <= oa -> oa + PQM.ASIZE <= hl_sptop L -> oa mod 8 = 0 -> sp <= ov -> ov + 56 <= hl_sptop L -> oa + PQM.ASIZE <= ov -> ov mod 8 = 0 ->
    sp <= osk -> osk + 24 <= hl_sptop L -> osk mod 8 = 0 -> ov + 56 <= osk ->
    sp <= oec -> oec + 16 <= hl_sptop L -> oec mod 8 = 0 -> oec + 16 <= oa ->             (* [comment removed for export] *)
    ae_at M oa ov osk st -> ae_ok st -> ec_state M oec b cat -> PMST.base_ok segs A M -> err_ok M e -> pre R M st ->
    PMSP.credit_le (pot_ae L st) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (st' : aest) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        ae_at M' oa ov osk st' -> ae_ok st' -> ec_state M' oec b' cat -> PMST.base_ok segs A M' -> err_ok M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> step R M st st' b b' ->
        L5C.hpres L LBX sp (pm_scr VIS_H) (ae_W A oa ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (pot_ae L st) (pot_ae L st') ->
        model_but_vm model model' -> hi_heap HI (aeown st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition step_val (dk dphi : Z) (ts : Prop) (st st' : aest) (b b' : bool) : Prop :=
  nlv st' = nlv st /\ kbsize st' <= kbsize st + dk /\ phi st' <= phi st + dphi /\ esize st' = esize st /\ edepth st' = edepth st /\ (b' = b \/ ts).
(* [comment removed for export] *)
Definition d_push (R : bvmap 5 word) : Z := Z.max 2 (hdr_cont (bv_unsigned (getr R 11%bv))).
Definition step_push (R : bvmap 5 word) (st st' : aest) (b b' : bool) : Prop :=
  nlv st' = nlv st + 1 /\ kbsize st' <= kbsize st + 2 /\ phi st' <= phi st + d_push R
  /\ esize st' - edepth st' = esize st - edepth st /\ esize st <= esize st' <= esize st + 1 /\ b' = b.
(* [comment removed for export] *)
Definition step_pop (st st' : aest) (b b' : bool) : Prop :=
  nlv st' = nlv st - 1 /\ kbsize st' <= kbsize st + 2 /\ phi st' <= phi st + 6 /\ esize st' <= esize st
  /\ (esize st' - edepth st' = esize st - edepth st \/ b' = true).

(* [comment removed for export] *)
Definition no_args (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop := True.
Definition args_ec4 (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop := getr R 14%bv = Z_to_bv 64 oec.
Definition args_ec3 (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop := getr R 13%bv = Z_to_bv 64 oec.
Definition args_ec2 (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop := getr R 12%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition pre_push (R : bvmap 5 word) (M : word -> option byte) (st : aest) : Prop :=
  nlv st <= PQM.MAX_DEPTH /\ kbsize st + 2 <= PQM.SMB /\ zsize st + 5 <= NESK.SMZ /\ esize st <= MAX_DEPTH.
(* [comment removed for export] *)
Definition pre_pop (R : bvmap 5 word) (M : word -> option byte) (st : aest) : Prop :=
  2 <= nlv st /\ kbsize st + 2 <= PQM.SMB /\ phi st + 6 <= NESK.SMZ.
(* [comment removed for export] *)
Definition pre_val (dk dphi : Z) (R : bvmap 5 word) (M : word -> option byte) (st : aest) : Prop :=
  kbsize st + dk <= PQM.SMB /\ zsize st + dphi <= NESK.SMZ.
(* [comment removed for export] *)
Definition is_esec (R : bvmap 5 word) : bool := Z.eqb (bv_unsigned (getr R 12%bv)) TAG_ESEC.
Definition d_u64 (R : bvmap 5 word) : Z := ndig (bv_unsigned (getr R 11%bv)) + 2.                 (* [comment removed for export] *)
Definition dphi_u64 (R : bvmap 5 word) : Z := if is_esec R then 15 else ndig (bv_unsigned (getr R 11%bv)) + 2.   (* [comment removed for export] *)
Definition d_i64 (R : bvmap 5 word) : Z := ndig (Z.abs (sval (bv_unsigned (getr R 11%bv)))) + 3.
Definition d_double : Z := WD.WD_MAX + 2.
Definition d_null : Z := 6.
Definition d_bool : Z := 7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition args_u64 (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop :=
  (getr R 12%bv = Z_to_bv 64 TAG_NONE \/ (getr R 12%bv = Z_to_bv 64 TAG_ESEC /\ bv_unsigned (getr R 11%bv) < 2 ^ 32)) /\ getr R 14%bv = Z_to_bv 64 oec.
Definition args_i64 (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop :=
  getr R 12%bv = Z_to_bv 64 TAG_NONE /\ getr R 14%bv = Z_to_bv 64 oec.
Definition args_bool (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop :=
  (getr R 11%bv = Z_to_bv 64 0 \/ getr R 11%bv = Z_to_bv 64 1) /\ getr R 14%bv = Z_to_bv 64 oec.
(* [comment removed for export] *)
Definition view_len (R : bvmap 5 word) (M : word -> option byte) (n : Z) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ L5.u64_at segs M (p + 8) n /\ 0 <= n < 2 ^ 26.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition args_str (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop :=
  exists p d n t bs, getr R 11%bv = Z_to_bv 64 p /\ sp <= p /\ p + 16 <= oa /\ view_ok M sp oa LBX p d n
  /\ getr R 12%bv = Z_to_bv 64 t /\ (t = TAG_NONE \/ t = TAG_ENANO) /\ getr R 14%bv = Z_to_bv 64 oec
  /\ L5.bytes_at segs M d bs /\ Z.of_nat (length bs) = n /\ utf8_valid bs = true /\ bytes_ok bs /\ (t = TAG_ENANO -> n <= 31).   (* [comment removed for export] *)
Definition args_view (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop :=
  exists p d n, getr R 11%bv = Z_to_bv 64 p /\ sp <= p /\ p + 16 <= oa /\ view_ok M sp oa LBX p d n /\ getr R 14%bv = Z_to_bv 64 oec.
Definition args_bstr_tag (R : bvmap 5 word) (M : word -> option byte) (sp oa oec : Z) (LBX : list (Z * Z)) : Prop :=
  args_view R M sp oa oec LBX /\ getr R 12%bv = Z_to_bv 64 0.
(* [comment removed for export] *)
Definition dphi_str (R : bvmap 5 word) (n : Z) : Z := if Z.eqb (bv_unsigned (getr R 12%bv)) TAG_ENANO then Z.max (n + 5) 15 else n + 5.
Definition pre_str (R : bvmap 5 word) (M : word -> option byte) (st : aest) : Prop :=
  exists n, view_len R M n /\ kbsize st + n + 4 <= PQM.SMB /\ zsize st + dphi_str R n <= NESK.SMZ.
Definition ts_str (R : bvmap 5 word) : Prop := getr R 12%bv = Z_to_bv 64 TAG_ENANO.
Definition step_str (R : bvmap 5 word) (M : word -> option byte) (st st' : aest) (b b' : bool) : Prop :=
  exists n, view_len R M n /\ step_val (n + 4) (dphi_str R n) (ts_str R) st st' b b'.
Definition pre_bstr (R : bvmap 5 word) (M : word -> option byte) (st : aest) : Prop :=
  exists n, view_len R M n /\ kbsize st + b64len n + 4 <= PQM.SMB /\ b64len n + 4 <= PQM.SMK /\ zsize st + Z.max (b64len n + 5) (n + 6) <= NESK.SMZ.
Definition step_bstr (R : bvmap 5 word) (M : word -> option byte) (st st' : aest) (b b' : bool) : Prop :=
  exists n, view_len R M n /\ step_val (b64len n + 4) (Z.max (b64len n + 5) (n + 6)) False st st' b b'.

(* [comment removed for export] *)
Definition v_begin_array_spec : Prop := vis_spec (qa_v_begin_array AQ) args_ec4 pre_push (fun R _ => step_push R).
Definition v_begin_object_spec : Prop := vis_spec (qa_v_begin_object AQ) args_ec4 pre_push (fun R _ => step_push R).
Definition v_end_array_spec : Prop := vis_spec (qa_v_end_array AQ) args_ec2 pre_pop (fun _ _ => step_pop).
Definition v_end_object_spec : Prop := vis_spec (qa_v_end_object AQ) args_ec2 pre_pop (fun _ _ => step_pop).
Definition v_uint64_spec : Prop :=
  vis_spec (qa_v_uint64 AQ) args_u64 (fun R M => pre_val (d_u64 R) (dphi_u64 R) R M) (fun R _ => step_val (d_u64 R) (dphi_u64 R) (is_esec R = true)).
Definition v_int64_spec : Prop :=
  vis_spec (qa_v_int64 AQ) args_i64 (fun R M => pre_val (d_i64 R) (d_i64 R) R M) (fun R _ => step_val (d_i64 R) (d_i64 R) False).
Definition v_double_spec : Prop := vis_spec (qa_v_double AQ) args_ec3 (pre_val d_double d_double) (fun _ _ => step_val d_double d_double False).
Definition v_null_spec : Prop := vis_spec (qa_v_null AQ) args_ec3 (pre_val d_null d_null) (fun _ _ => step_val d_null d_null False).
Definition v_bool_spec : Prop := vis_spec (qa_v_bool AQ) args_bool (pre_val d_bool d_bool) (fun _ _ => step_val d_bool d_bool False).
Definition v_string_spec : Prop := vis_spec (qa_v_string AQ) args_str pre_str step_str.
Definition v_bstr_tag_spec : Prop := vis_spec (qa_v_bstr_tag AQ) args_bstr_tag pre_bstr step_bstr.
Definition v_bstr_raw_spec : Prop := vis_spec (qa_v_bstr_raw AQ) args_view pre_bstr step_bstr.
Definition v_flush_spec : Prop := vis_spec (qa_v_flush AQ) no_args (fun _ _ _ => True) (fun _ _ => step_val 0 0 False).

(* [comment removed for export] *)
Record vis_ok : Prop := VISOK {
  vo_begin_array : v_begin_array_spec; vo_begin_object : v_begin_object_spec;
  vo_end_array : v_end_array_spec; vo_end_object : v_end_object_spec;
  vo_uint64 : v_uint64_spec; vo_int64 : v_int64_spec; vo_double : v_double_spec;
  vo_null : v_null_spec; vo_bool : v_bool_spec; vo_string : v_string_spec;
  vo_bstr_tag : v_bstr_tag_spec; vo_bstr_raw : v_bstr_raw_spec; vo_flush : v_flush_spec }.

End Specs.
End PNV.

End PnVisN.
Module WdGnum.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.WdLibc.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition alldig (bs : list Z) : Prop := Forall (fun c => WDL.isdig c = true) bs.
Definition nodig_head (bs : list Z) : Prop := match bs with [] => True | c :: _ => WDL.isdig c = false end.

Lemma skip_app ds rest : alldig ds -> WDL.skip_digits (ds ++ rest) = WDL.skip_digits rest.
Proof. induction 1 as [|c ds Hc _ IH]; [reflexivity|]. cbn [app WDL.skip_digits]. rewrite Hc. exact IH. Qed.
Lemma skip_nodig rest : nodig_head rest -> WDL.skip_digits rest = rest.
Proof. destruct rest as [|c r]; [reflexivity|]. cbn. intros ->. reflexivity. Qed.
Lemma ndig_app ds rest : alldig ds -> nodig_head rest -> WDL.ndig (ds ++ rest) = length ds.
Proof. intros H N. unfold WDL.ndig. rewrite skip_app by exact H. rewrite skip_nodig by exact N. rewrite length_app. lia. Qed.

(* [comment removed for export] *)
Lemma gnum_tail_e sg dse : (sg = 43 \/ sg = 45) -> alldig dse -> (2 <= length dse)%nat -> WDL.gnum_tail (101 :: sg :: dse) = true.
Proof.
  intros Hs Hd Hl. unfold WDL.gnum_tail. change (101 =? 101) with true. cbn [andb]. unfold WDL.gnum_exp.
  replace ((sg =? 43) || (sg =? 45)) with true by (destruct Hs as [-> | ->]; reflexivity). cbn [andb].
  pose proof (ndig_app dse [] Hd I) as N. rewrite app_nil_r in N. rewrite N.
  pose proof (skip_app dse [] Hd) as S. rewrite app_nil_r in S. rewrite S.
  change (WDL.skip_digits []) with (@nil Z). change (length (@nil Z) =? 0)%nat with true. rewrite Bool.andb_true_r. apply Nat.leb_le. lia.
Qed.

(* [comment removed for export] *)
Lemma gnum_body (neg : bool) d1 (dot : bool) d2 T :
  alldig d1 -> (1 <= length d1)%nat -> alldig d2 -> (dot = true -> (1 <= length d2)%nat) ->
  WDL.gnum_tail T = true -> nodig_head T -> match T with c :: _ => c <> 46 | [] => True end ->
  WDL.gnum ((if neg then [45] else []) ++ d1 ++ (if dot then 46 :: d2 else []) ++ T) = true.
Proof.
  intros H1 L1 H2 Ld HT NT N46.
  assert (E : WDL.gnum ((if neg then [45] else []) ++ d1 ++ (if dot then 46 :: d2 else []) ++ T) =
              (Nat.leb 1 (WDL.ndig (d1 ++ (if dot then 46 :: d2 else []) ++ T)) && WDL.gnum_frac (WDL.skip_digits (d1 ++ (if dot then 46 :: d2 else []) ++ T)))).
  { unfold WDL.gnum. cbv zeta. destruct neg; cbn [app].
    - change (45 =? 45) with true. cbv iota. reflexivity.
    - destruct d1 as [|c d1']; [cbn in L1; lia|]. cbn [app]. apply Forall_cons_iff in H1. destruct H1 as [Hc _].
      replace (c =? 45) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intros ->. cbv in Hc. discriminate. }
  rewrite E. clear E.
  assert (NR : nodig_head ((if dot then 46 :: d2 else []) ++ T)) by (destruct dot; [reflexivity | exact NT]).
  rewrite ndig_app by assumption. rewrite skip_app by assumption. rewrite skip_nodig by assumption.
  apply andb_true_intro. split; [apply Nat.leb_le; lia|].
  destruct dot; cbn [app].
  - cbn [WDL.gnum_frac]. rewrite Z.eqb_refl. rewrite ndig_app by assumption. rewrite skip_app by assumption. rewrite skip_nodig by assumption.
    apply andb_true_intro. split; [apply Nat.leb_le; auto | exact HT].
  - destruct T as [|c r]; [reflexivity|]. cbn [WDL.gnum_frac]. rewrite (proj2 (Z.eqb_neq c 46) N46). exact HT.
Qed.

End WdGnum.
