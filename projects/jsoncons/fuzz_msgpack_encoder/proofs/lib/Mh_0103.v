(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module PmSpecsX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSX.
Import PMSP.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition reader_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
    hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> model_ok model -> K [] -> entry A L R M sp r 11 -> frame_ok A L sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p A fb) -> getr R 11%bv = Z_to_bv 64 (o_ec A fb) ->
    run_pre segs A M fb s str sm e -> incl (PM.vs_own str) LBX -> (1 <= length (PM.p_stk s))%nat -> ec_at segs M (o_ec A fb) 0 cat ->
    PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (PM.pot_parser L (pst_reset s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        parse_post segs A M' fb (pst_reset s) s' str sm sm' e e' ->
        L5C.hpres L LBX sp (pm_scr 11) (W_run A fb) M M' ->
        credit_keep cr cr' (PM.pot_parser L (pst_reset s)) cr0 ->
        model_but_vm model model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg segs R' r M' model') K) ->
    srealizes segs SCFG (cfg segs R (pa_reader_read A) M model) K.

(* [comment removed for export] *)
Definition vec_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PM.pstate),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] -> entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= hl_sptop L -> L5.u64_at segs M t v ->
    sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 -> L5.defined M v 24 ->
    PM.vec_at segs T3 T4 M v b k stk -> In (b, 32 * 2 ^ k) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove b LB) sp (pm_scr 0) [(v, 24)] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove b LB) cr M' (m_vmmaps model') ->
        srealizes segs SCFG (cfg segs R' r M' model') K) ->
    srealizes segs SCFG (cfg segs R (pa_vec_dtor A) M model) K.

End Specs.
End PMSX.

End PmSpecsX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require HnIface.
Module PnHeapR.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require Export HnIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSR.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Definition OPNEW_SCR : Z := 16 + 8224.
Definition OPDEL_SCR : Z := 8224.
Definition NMAXR : Z := 2 ^ 27.

(* [comment removed for export] *)
Definition opnewR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAXR -> credit_okR cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pa_opnew A) M model) K.

(* [comment removed for export] *)
Definition opdelR_spec_at (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (B n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    In (B, n) LB -> getr R 10%bv = Z_to_bv 64 B ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove B LB) sp OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove B LB) (refundR cr n) M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Definition opdelR_spec : Prop := opdelR_spec_at (pa_opdel A).
Definition opdelR_sized_spec : Prop := opdelR_spec_at (pa_opdel_sized A).
End Specs.

(* [comment removed for export] *)
Lemma hi_heap_clientR {bmK : BMode} L scfg HI LB cr M M' VM :   (* [comment removed for export] *)
  heap_ifaceR_ok L scfg HI -> hi_heap HI LB cr M VM ->
  (forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a) ->
  hl_img_hi L <= 0x7fff7f800000 -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ (hl_ceil L <= a < hl_sptop L) \/ in_block LB a) ->
  mem_grows M M' -> hi_heap HI LB cr M' VM.
Proof.
  intros HIok HH Hro Hhi Hsp Hchg Hgr. eapply (hir_frame L scfg HI HIok). exact HH.
  - intros a Ha Hpriv. destruct (Hchg a Ha) as [E|[S|B]]. exact E.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. lia. apply Hro in P. lia.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. exact (P2 B). apply Hro in P.
      destruct B as (b & Hb & Hin). pose proof (proj1 (hir_wf L scfg HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
      lia.
  - intros x Hx. apply Hgr. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma refund_debitR cr n : refundR (debitR cr n) n = cr.
Proof. exact (refund_debit cr n). Qed.
Lemma debitR_comm cr n m : debitR (debitR cr n) m = debitR (debitR cr m) n.
Proof. unfold debitR. cbn. f_equal; lia. Qed.
Lemma refundR_comm cr n m : refundR (refundR cr n) m = refundR (refundR cr m) n.
Proof. unfold refundR. cbn. f_equal; lia. Qed.
Lemma refundR_debitR_comm cr n m : refundR (debitR cr n) m = debitR (refundR cr m) n.
Proof. unfold refundR, debitR. cbn. f_equal; lia. Qed.
Lemma credit_okR_mono cr cr' n : credit_okR cr n -> fst cr <= fst cr' -> snd cr <= snd cr' -> credit_okR cr' n.
Proof. unfold credit_okR. intros [A B] C D. split; lia. Qed.
(* [comment removed for export] *)
Lemma credit_okR_small cr n : 0 <= n <= 2 ^ 20 - 20 -> 1 <= fst cr -> 2 ^ 20 <= snd cr -> credit_okR cr n.
Proof. intros Hn H1 H2. unfold credit_okR. rewrite (cszR_small n Hn). split; lia. Qed.
Lemma debitR_small cr n : 0 <= n <= 2 ^ 20 - 20 -> debitR cr n = (fst cr - 1, snd cr - 2 ^ 20).
Proof. intros Hn. unfold debitR. rewrite (cszR_small n Hn). reflexivity. Qed.
Lemma refundR_small cr n : 0 <= n <= 2 ^ 20 - 20 -> refundR cr n = (fst cr + 1, snd cr + 2 ^ 20).
Proof. intros Hn. unfold refundR. rewrite (cszR_small n Hn). reflexivity. Qed.
End PMSR.

End PnHeapR.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.
Module VdSpec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.WdLibc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module VD.

Definition G_SCR : Z := 128.      (* [comment removed for export] *)
Definition G_BUF : Z := 22.       (* [comment removed for export] *)

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

Definition grisu3_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (buf lenp kp u sp r : Z),
    PMSP.model_ok model -> K [] ->
    WDL.entry_scr A L R M sp r G_SCR ->
    getr R 10%bv = Z_to_bv 64 buf -> getr R 11%bv = Z_to_bv 64 lenp -> getr R 12%bv = Z_to_bv 64 kp ->
    getr (@fp_regs fx) 10%bv = Z_to_bv 64 u -> 1 <= u < 2 ^ 63 ->
    sp <= buf -> buf + G_BUF <= hl_sptop L -> L5.defined M buf G_BUF ->
    sp <= lenp -> lenp + 4 <= hl_sptop L -> L5.defined M lenp 4 ->
    sp <= kp -> kp + 4 <= hl_sptop L -> L5.defined M kp 4 ->
    (kp + 4 <= buf \/ buf + G_BUF <= kp) -> (lenp + 4 <= buf \/ buf + G_BUF <= lenp) -> (kp + 4 <= lenp \/ lenp + 4 <= kp) ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (res len k : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 res -> (res = 0 \/ res = 1) ->
        L5.u32_at segs M' lenp len -> 1 <= len <= 21 -> L5.u32_at segs M' kp k -> -343 <= k <= 309 ->
        WDL.mframe L sp G_SCR [(buf, G_BUF); (lenp, 4); (kp, 4)] M M' -> PMST.base_ok segs A M' ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

End Specs.

(* [comment removed for export] *)
Definition FE_SCR : Z := 14368.     (* [comment removed for export] *)
Definition PR_SCR : Z := 14432.     (* [comment removed for export] *)
Definition DB_SCR : Z := 14432.     (* [comment removed for export] *)
Definition DS_SCR : Z := 10320.     (* [comment removed for export] *)
Definition DGF_SCR : Z := 14592.    (* [comment removed for export] *)
Definition DGT_SCR : Z := 14736.    (* [comment removed for export] *)
Definition FE_MAX : Z := 4.         (* [comment removed for export] *)
Definition PR_MAX : Z := 27.        (* [comment removed for export] *)
Definition DB_MAX : Z := 28.        (* [comment removed for export] *)
Definition DG_MAX : Z := 28.        (* [comment removed for export] *)

Section Sink.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable sst : Type.
Variable str_at : (word -> option byte) -> Z -> sst -> Prop.
Variable str_own : sst -> list (Z * Z).
Variable str_size : sst -> Z.
Variable str_pot : sst -> credit.

(* [comment removed for export] *)
Definition pusher (pc scr mx : Z) (pre : bvmap 5 word -> (word -> option byte) -> Z -> Z -> Z -> Prop) (post : bvmap 5 word -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (so os sp r : Z) (x : sst),
    hi_heap HI (str_own x ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    WD.entry_scr A L R M sp r scr ->
    pre R M so os sp ->
    L5.u64_at segs M so os -> str_at M os x -> str_size x + mx <= WD.STR_MAX ->
    sp <= so -> so + 8 <= hl_sptop L -> sp <= os -> os + 24 <= hl_sptop L -> WD.apart24 so 8 os ->
    PMST.base_ok segs A M -> PMSP.credit_le (str_pot x) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : sst) (cr' : credit),
        regs_preserved R R' -> post R' -> str_at M' os x' -> str_size x <= str_size x' <= str_size x + mx ->
        L5C.hpres L LBX sp scr [(os, 24)] M M' -> PMSP.credit_keep cr cr' (str_pot x) (str_pot x') ->
        model_but_vm model model' -> hi_heap HI (str_own x' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition rbuf (M : word -> option byte) (sp p n os : Z) : Prop :=
  sp <= p /\ p + n <= hl_sptop L /\ L5.defined M p n /\ WD.apart24 p n os.

(* [comment removed for export] *)
Definition fe_spec (pc : Z) : Prop :=
  pusher pc FE_SCR FE_MAX
    (fun R _ so _ _ => exists k, getr R 10%bv = Z_to_bv 64 k /\ -999 <= k <= 999 /\ getr R 11%bv = Z_to_bv 64 so)
    (fun _ => True).

(* [comment removed for export] *)
Definition pr_spec (pc : Z) : Prop :=
  pusher pc PR_SCR PR_MAX
    (fun R M so os sp => exists buf len k, getr R 10%bv = Z_to_bv 64 buf /\ getr R 11%bv = Z_to_bv 64 len /\ getr R 12%bv = Z_to_bv 64 k
        /\ getr R 13%bv = Z_to_bv 64 (-4) /\ getr R 14%bv = Z_to_bv 64 17 /\ getr R 15%bv = Z_to_bv 64 so
        /\ 1 <= len <= 21 /\ -400 <= k <= 400 /\ rbuf M sp buf G_BUF os)
    (fun _ => True).

(* [comment removed for export] *)
Definition db_spec (pc : Z) : Prop :=
  pusher pc DB_SCR DB_MAX
    (fun R M so os sp => exists buf n dp, getr R 10%bv = Z_to_bv 64 buf /\ getr R 11%bv = Z_to_bv 64 n /\ getr R 12%bv = Z_to_bv 64 dp /\ getr R 13%bv = Z_to_bv 64 so
        /\ 0 <= n <= WDL.SNP_MAX /\ 0 <= dp < 256 /\ rbuf M sp buf n os)
    (fun _ => True).

(* [comment removed for export] *)
Definition dgf_spec (pc : Z) : Prop :=
  pusher pc DGF_SCR DG_MAX
    (fun R _ so _ _ => exists dp, getr R 10%bv = Z_to_bv 64 dp /\ 0 <= dp < 256 /\ getr R 11%bv = Z_to_bv 64 so)
    (fun R' => getr R' 10%bv = Z_to_bv 64 1).

(* [comment removed for export] *)
Definition dgt_spec (pc : Z) : Prop :=
  pusher pc DGT_SCR DG_MAX
    (fun R _ so _ _ => exists dp, getr R 10%bv = Z_to_bv 64 dp /\ 0 <= dp < 256 /\ getr R 11%bv = Z_to_bv 64 so)
    (fun R' => getr R' 10%bv = Z_to_bv 64 1).

(* [comment removed for export] *)
Definition wd_ok_stmt (pb_pc sn_pc fmt st_pc wd_pc : Z) : Prop :=
  WD.push_back_spec segs A L HI sst str_at str_own str_size str_pot pb_pc -> WDL.snprintf_spec segs A L sn_pc fmt -> WDL.strtod_spec segs A L st_pc ->
  WD.wd_spec segs A L HI sst str_at str_own str_size str_pot wd_pc.

End Sink.

Section NoSink.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

(* [comment removed for export] *)
Definition ds_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (s n valp sp r : Z) (bs : list Z),
    PMSP.model_ok model -> K [] ->
    WDL.entry_scr A L R M sp r DS_SCR ->
    getr R 10%bv = Z_to_bv 64 s -> getr R 11%bv = Z_to_bv 64 n -> getr R 12%bv = Z_to_bv 64 valp ->
    Z.of_nat (length bs) = n -> 1 <= n <= WDL.SNP_MAX -> (WDL.gnum bs = true \/ WDL.gspecial bs) -> L5.bytes_at segs M s (bs ++ [0]) ->
    sp <= s -> s + n + 1 <= hl_sptop L -> sp <= valp -> valp + 8 <= hl_sptop L -> L5.defined M valp 8 -> (valp + 8 <= s \/ s + n + 1 <= valp) ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (ec : Z),
        regs_preserved R R' -> WDL.fregs_preserved fx fx' -> getr R' 11%bv = Z_to_bv 64 ec -> (ec = 0 \/ ec = 34) ->
        L5.bytes_at segs M' s (bs ++ [0]) ->
        WDL.mframe L sp DS_SCR [(valp, 8)] M M' -> PMST.base_ok segs A M' ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
End NoSink.

End VD.

End VdSpec.
Module VdSpecC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.WdLibc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.VdSpec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module VDC.

(* [comment removed for export] *)
Definition ascii (bs : list Z) : Prop := Forall (fun b => 0 <= b < 128) bs.
(* [comment removed for export] *)
Definition dch (b : Z) : Prop := 46 <= b <= 57.
(* [comment removed for export] *)
Definition digits_at (segs : list Segment) (M : word -> option byte) (buf len : Z) : Prop :=
  exists cs, L5.bytes_at segs M buf cs /\ length cs = 22%nat /\ forall i, (i < Z.to_nat len)%nat -> dch (nth i cs 0).

Lemma digits_at_agree segs M M' buf len : digits_at segs M buf len -> 0 <= buf -> buf + 22 <= 2 ^ 64 -> L5C.agree_on M M' buf 22 -> digits_at segs M' buf len.
Proof.
  intros (cs & BA & LEN & FA) H0 H1 AG. exists cs. split; [| split; [exact LEN| exact FA]].
  apply (L5C.bytes_at_agree segs M M' buf cs); [rewrite LEN; exact AG| exact H0| rewrite LEN; exact H1| exact BA].
Qed.
Lemma ascii_nil : ascii []. Proof. constructor. Qed.
Lemma ascii_app a b : ascii a -> ascii b -> ascii (a ++ b). Proof. intros Ha Hb. apply Forall_app. split; assumption. Qed.
Lemma ascii_snoc a c : ascii a -> 0 <= c < 128 -> ascii (a ++ [c]). Proof. intros Ha Hc. apply ascii_app; [exact Ha| constructor; [exact Hc| constructor]]. Qed.
Lemma ascii_of_dch c : dch c -> 0 <= c < 128. Proof. unfold dch. lia. Qed.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

(* [comment removed for export] *)
Definition grisu3_specC (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (buf lenp kp u sp r : Z),
    PMSP.model_ok model -> K [] ->
    WDL.entry_scr A L R M sp r VD.G_SCR ->
    getr R 10%bv = Z_to_bv 64 buf -> getr R 11%bv = Z_to_bv 64 lenp -> getr R 12%bv = Z_to_bv 64 kp ->
    getr (@fp_regs fx) 10%bv = Z_to_bv 64 u -> 1 <= u < 2 ^ 63 ->
    sp <= buf -> buf + VD.G_BUF <= hl_sptop L -> L5.defined M buf VD.G_BUF ->
    sp <= lenp -> lenp + 4 <= hl_sptop L -> L5.defined M lenp 4 ->
    sp <= kp -> kp + 4 <= hl_sptop L -> L5.defined M kp 4 ->
    (kp + 4 <= buf \/ buf + VD.G_BUF <= kp) -> (lenp + 4 <= buf \/ buf + VD.G_BUF <= lenp) -> (kp + 4 <= lenp \/ lenp + 4 <= kp) ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (res len k : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 res -> (res = 0 \/ res = 1) ->
        L5.u32_at segs M' lenp len -> 1 <= len <= 21 -> L5.u32_at segs M' kp k -> -343 <= k <= 309 ->
        digits_at segs M' buf len ->
        WDL.mframe L sp VD.G_SCR [(buf, VD.G_BUF); (lenp, 4); (kp, 4)] M M' -> PMST.base_ok segs A M' ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
End Specs.

Section Sink.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable sst : Type.
Variable str_at : (word -> option byte) -> Z -> sst -> Prop.
Variable str_own : sst -> list (Z * Z).
Variable str_size : sst -> Z.
Variable str_pot : sst -> credit.
Variable str_txt : sst -> list Z.

(* [comment removed for export] *)
Definition str_keepC : Prop :=
  forall (M M' Mh : word -> option byte) (os : Z) (x : sst) (LBX : list (Z * Z)) (cr : credit) (VM : VmMaps) (P : Z -> Prop),
    0 <= os -> os + 24 <= 2 ^ 64 -> hl_sptop L <= 2 ^ 47 -> hi_heap HI (str_own x ++ LBX) cr Mh VM -> mem_grows M M' ->
    (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall i, P i -> (hl_ceil L <= i < os) \/ in_errno L i) ->
    L5C.agree_on M M' os 24 ->
    str_at M os x -> str_at M' os x.

(* [comment removed for export] *)
Definition push_back_specC (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (os c sp r : Z) (x : sst),
    hi_heap HI (str_own x ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    WD.entry_scr A L R M sp r WD.PB_SCR ->
    getr R 10%bv = Z_to_bv 64 os -> getr R 11%bv = Z_to_bv 64 c -> 0 <= c < 128 ->
    str_at M os x -> str_size x < WD.STR_MAX -> sp <= os -> os + 24 <= hl_sptop L ->
    PMST.base_ok segs A M -> PMSP.credit_le (str_pot x) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : sst) (cr' : credit),
        regs_preserved R R' -> str_at M' os x' -> str_size x' = str_size x + 1 -> str_txt x' = str_txt x ++ [c] ->
        L5C.hpres L LBX sp WD.PB_SCR [(os, 24)] M M' -> PMSP.credit_keep cr cr' (str_pot x) (str_pot x') ->
        model_but_vm model model' -> hi_heap HI (str_own x' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition pusherC (pc scr mx : Z) (pre : bvmap 5 word -> (word -> option byte) -> Z -> Z -> Z -> Prop) (post : bvmap 5 word -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (so os sp r : Z) (x : sst),
    hi_heap HI (str_own x ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    WD.entry_scr A L R M sp r scr ->
    pre R M so os sp ->
    L5.u64_at segs M so os -> str_at M os x -> str_size x + mx <= WD.STR_MAX ->
    sp <= so -> so + 8 <= hl_sptop L -> sp <= os -> os + 24 <= hl_sptop L -> WD.apart24 so 8 os ->
    PMST.base_ok segs A M -> PMSP.credit_le (str_pot x) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : sst) (cr' : credit),
        regs_preserved R R' -> post R' -> str_at M' os x' -> str_size x <= str_size x' <= str_size x + mx ->
        (exists ds, str_txt x' = str_txt x ++ ds /\ ascii ds) ->
        L5C.hpres L LBX sp scr [(os, 24)] M M' -> PMSP.credit_keep cr cr' (str_pot x) (str_pot x') ->
        model_but_vm model model' -> hi_heap HI (str_own x' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

Definition fe_specC (pc : Z) : Prop :=
  pusherC pc VD.FE_SCR VD.FE_MAX
    (fun R _ so _ _ => exists k, getr R 10%bv = Z_to_bv 64 k /\ -999 <= k <= 999 /\ getr R 11%bv = Z_to_bv 64 so)
    (fun _ => True).

(* [comment removed for export] *)
Definition pr_specC (pc : Z) : Prop :=
  pusherC pc VD.PR_SCR VD.PR_MAX
    (fun R M so os sp => exists buf len k, getr R 10%bv = Z_to_bv 64 buf /\ getr R 11%bv = Z_to_bv 64 len /\ getr R 12%bv = Z_to_bv 64 k
        /\ getr R 13%bv = Z_to_bv 64 (-4) /\ getr R 14%bv = Z_to_bv 64 17 /\ getr R 15%bv = Z_to_bv 64 so
        /\ 1 <= len <= 21 /\ -400 <= k <= 400 /\ VD.rbuf L M sp buf VD.G_BUF os /\ digits_at segs M buf len)
    (fun _ => True).

Definition db_specC (pc : Z) : Prop :=
  pusherC pc VD.DB_SCR VD.DB_MAX
    (fun R M so os sp => exists buf n dp, getr R 10%bv = Z_to_bv 64 buf /\ getr R 11%bv = Z_to_bv 64 n /\ getr R 12%bv = Z_to_bv 64 dp /\ getr R 13%bv = Z_to_bv 64 so
        /\ 0 <= n <= WDL.SNP_MAX /\ 0 <= dp < 256 /\ VD.rbuf L M sp buf n os)
    (fun _ => True).

Definition dgf_specC (pc : Z) : Prop :=
  pusherC pc VD.DGF_SCR VD.DG_MAX
    (fun R _ so _ _ => exists dp, getr R 10%bv = Z_to_bv 64 dp /\ 0 <= dp < 256 /\ getr R 11%bv = Z_to_bv 64 so)
    (fun R' => getr R' 10%bv = Z_to_bv 64 1).

Definition dgt_specC (pc : Z) : Prop :=
  pusherC pc VD.DGT_SCR VD.DG_MAX
    (fun R _ so _ _ => exists dp, getr R 10%bv = Z_to_bv 64 dp /\ 0 <= dp < 256 /\ getr R 11%bv = Z_to_bv 64 so)
    (fun R' => getr R' 10%bv = Z_to_bv 64 1).

(* [comment removed for export] *)
Definition wd_specC (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (o so os sp r : Z) (x : sst),
    hi_heap HI (str_own x ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    WD.entry_scr A L R M sp r WD.WD_SCR ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 so ->
    WD.wd_at segs M o -> L5.u64_at segs M so os -> str_at M os x -> str_size x + WD.WD_MAX <= WD.STR_MAX ->
    sp <= o -> o + 12 <= hl_sptop L -> sp <= so -> so + 8 <= hl_sptop L -> sp <= os -> os + 24 <= hl_sptop L ->
    WD.apart24 o 12 os -> WD.apart24 so 8 os ->
    PMST.base_ok segs A M -> PMSP.credit_le (str_pot x) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : sst) (cr' : credit),
        regs_preserved R R' -> str_at M' os x' -> str_size x <= str_size x' <= str_size x + WD.WD_MAX ->
        (exists ds, str_txt x' = str_txt x ++ ds /\ ascii ds) ->
        L5C.hpres L LBX sp WD.WD_SCR [(os, 24)] M M' -> PMSP.credit_keep cr cr' (str_pot x) (str_pot x') ->
        model_but_vm model model' -> hi_heap HI (str_own x' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

Definition wd_ok_stmtC (pb_pc sn_pc fmt st_pc wd_pc : Z) : Prop :=
  push_back_specC pb_pc -> WDL.snprintf_spec segs A L sn_pc fmt -> WDL.strtod_spec segs A L st_pc -> wd_specC wd_pc.

End Sink.
End VDC.

End VdSpecC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef.
Module PnCValSpecW.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVSW.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

Definition validate_fun_specW (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (p n sp r : Z) (l : list Z),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 29 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n ->
    (n = 0 \/ sp <= p \/ p + n <= sp - PMSP.pm_scr 0) ->
    PMST.base_ok segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (v : Z),
        regs_preserved R R' -> L5.frame_but [(sp - PMSP.pm_scr 0, PMSP.pm_scr 0)] M M' -> mem_grows M M' ->
        getr R' 11%bv = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model) K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.

(* [comment removed for export] *)
Lemma scan_of_fun pc : validate_fun_specW pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (p n sp r : Z) (l : list Z),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 29 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n ->
    (n = 0 \/ sp <= p \/ p + n <= sp - PMSP.pm_scr 0) ->
    PMST.base_ok segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> L5.frame_but [(sp - PMSP.pm_scr 0, PMSP.pm_scr 0)] M M' -> mem_grows M M' ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model) K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Proof.
  intros VF fx R M model K p n sp r l H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 KONT.
  eapply (VF fx R M model K p n sp r l); try eassumption.
  intros fx' R' M' v P1 P2 P3 _ _ _. exact (KONT fx' R' M' P1 P2 P3).
Qed.
End Specs.
End PECVSW.

End PnCValSpecW.
Module PnCValSpec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.

Definition validate_fun_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (p n sp r : Z) (l : list Z),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n ->
    (n = 0 \/ sp <= p \/ p + n <= sp - PMSP.pm_scr 0) ->
    PMST.base_ok segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (v : Z),
        regs_preserved R R' -> L5.frame_but [(sp - PMSP.pm_scr 0, PMSP.pm_scr 0)] M M' -> mem_grows M M' ->
        getr R' 11%bv = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model) K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.

(* [comment removed for export] *)
Lemma scan_of_fun pc : validate_fun_spec pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (p n sp r : Z) (l : list Z),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> PMSP.entry A L R M sp r 0 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n ->
    (n = 0 \/ sp <= p \/ p + n <= sp - PMSP.pm_scr 0) ->
    PMST.base_ok segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        regs_preserved R R' -> L5.frame_but [(sp - PMSP.pm_scr 0, PMSP.pm_scr 0)] M M' -> mem_grows M M' ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model) K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Proof.
  intros VF fx R M model K p n sp r l H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 KONT.
  eapply (VF fx R M model K p n sp r l); try eassumption.
  intros fx' R' M' v P1 P2 P3 _ _ _. exact (KONT fx' R' M' P1 P2 P3).
Qed.
End Specs.
End PECVS.

End PnCValSpec.
From stdpp Require list. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module PnMpOwner.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From stdpp Require Import list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnMpOwner () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List9in_app_orC47Corelib4Init5Logic6eq_indc69OSSVerify5KrLib7Mh_01036VdSpec2VD6pusherC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD>push_back_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List8nil_consK47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic5False00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List2hdC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5PSIZEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List9in_or_appc69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW5apartC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9mrest_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS7W_srcfGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_SRCC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implc69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW5namedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW<frame_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW;outside_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW<outside_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW;outside_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW>outside_ForallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW8chunk_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW:named_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C:hpres_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_sbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_skC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_bbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86v8_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_tbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW7rest_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3PSZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW:blk_clientC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List>NoDup_cons_iffC47Corelib4Init5Logic6eq_symc69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW>wsrcf_in_frameC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW6stk_inC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib7Mh_00906L5Core3L5C:hpres_cdefC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF3dkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8with_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028PnQModel3PQM4mpst01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01024PnV84PQV82v802C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8mvec_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW8named_agC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF8vs_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW7blk_dkrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW8stk_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF@mparser_at_frameC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4mpst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV82v800C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM6mstate00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW9frame_dkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8OFF_MAXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6OFF_TBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6OFF_BBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_STKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW=frame_clientBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW:cellB_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW;blk_clientBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM<vec_rest_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9vec_ownerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM;with_src_bbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7p_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_tgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_stkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW8cellB_agC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF7dkr_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW8blkB_dkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF<vstr_at_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW9blkB_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMFDmparser_at_frame_genC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7mvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9MAX_DEPTHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW:frameB_dkrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC35stdpp4base?NoDup_ListNoDupC46Stdlib5Lists4ListBNoDup_app_remove_rc69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW<in_lb_removeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_01028PnQModel3PQM9src_ownerC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00905PgSrc3PGS8owner_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_winC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6W_srcGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW9heapX_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW;heapX_nodupC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW;heapX_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW=src_owner_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00905PgSrc3PGS8owner_ok01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I69OSSVerify5KrLib7Mh_01024PnV84PQV89vowner_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vw_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_ovC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW=vec_owner_updC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01024PnV84PQV89vowner_ok01C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQOW.

Definition apart (p k q m : Z) : Prop := p + k <= q \/ q + m <= p.

Lemma outside_app W1 W2 a : L5.outside W1 a -> L5.outside W2 a -> L5.outside (W1 ++ W2) a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) [] "h02Hrh12W1h22W2h31ah42H1h52H2h61rp;1p;2p;3p;5p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0p10020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g003gR4p4p710R0p1004Ep4p710R5p8p1004ap4p771111110p1005^p4p771111110p8g006cR6p4p70R7P2p8P7P5p8P7P0p8P7P3p8P7g007_R3p4p710p8P7p1008<p4p710p8p1008Yp4p7210P5p8g0096j18Tg009Vj21TP3j32TP4j57Tg00:TR4j26Tg00:nj24Tg00;kj13TP1j35Tf1R1f0R3556p=0%86R5g00<DR7f2R0/131101f5R2f4R8526,03P6f6R9P2P1P3D710191012'6P4f7R4,001009f3R:/49#3P3f8,0:P9P8P3O2W0P3O110:4P2P8P3O2W0P3O1n200100000021000010000b0W0X66A268:/10eW5W4X37X25X15P0P1P3O3W3X25W1o"). Qed.
Lemma outside_cons r W a : ~ L5.in_rng r a -> L5.outside W a -> L5.outside (r :: W) a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) [] "h01Hh11Wh21ah31rh42r'h52H1h62H2h72Hrp;1p;2p;3p;6p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0p10020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R4g004ER0p4p710R5p8p1004ap4p771111110p1005^p4p771111110p8g006cR6p4p70R7P2p8P7P5p8P7P4p8P7P3p8P7p1007_p4p710p8P7p1008<p4p710p8p1008Yp4p7210P5p8g0096j17Tg00:nj22Tg00;kj10Tg009Vj23Tg00=?j35TP1j31Tg00=_j34TP0j66T%76R0g00<DR1f2R5f0R7'2#0f1R3,35f5R4f4R25569167g00:Tf6R8=463A16341254#0P7f7R9=465P6f81279#0X46P4f3R4P7E6W0P7O1A1658P2P4P7O2W7P7O1n200100000021000010000W0X46A5624/35eW6W5X21X10X36P5P3P7O3W2W1X36o"). Qed.
Lemma outside_nil a : L5.outside [] a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) [] "h01ah11Hh21rp;1p;3p;2p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0p10020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R4p1004Ep4p710R0p8p1004ap4p771111110p1005^p4p771111110p8g006cR5p4p70R6P2p8P6P0p8P6P4p8P6P3p8P6p1007_p4p710p8P6p1008<p4p710p8p1008Yp4p7210P0p8g00>9j14TP1j33Tg00:nj20Tg00;kj11Tg009Vj22Tg00<DR1f0R0%45R6535g00>Yf2f3'0#1P0n010000000W1X251260eX01P0O1W0o"). Qed.
Lemma outside_Forall W a : Forall (fun r => ~ L5.in_rng r a) W -> L5.outside W a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) [] "h01rh11Fh21Wh31ah41xh52Hrh65lemmap;1p;2p;3p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0g001OR3p4p710R4p8P0p10020R5p4p710p8P0P5p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R5p1004Ep4p710R0p8p1004ap4p771111110p1005^p4p771111110p8g006cR6p4p70R7P2p8P7P0p8P7P5p8P7P4p8P7p1007_p4p710p8P7g00?6R7p4p710p8p1008Yp4p7210P0p8g0096j18Tg00:nj20Tg00;kj11TP3j32TP1j33Tg00?Xj27Tg00@1j36TP7j34Tg009Vj25T%86R7g00<DR1f0R3f1R0'0#1X06=260f39363f4R4,03#1X06R5=264f5R29363f6R8,03#1X06P0O1[^46R9'71032#1X06=262A3638f7,03#1X06P0O1[^46;63W6A4654f2R5O2P9P3P5P0O2b1W5X061550eW1X31X27P0P3O2W3W2o"). Qed.

Local Ltac lu := unfold PQM.PSIZE, PQM.OFF_SRC, PQM.OFF_MAXD, PQM.OFF_TB, PQM.OFF_BB, PQM.OFF_STK in *; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Upd.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variable L : heap_layout.
Variables (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte).
Variables (op ois lo hi : Z) (s : PQM.mpst) (src src' : PM.srcst).

Let X : list (Z * Z) := PM.src_own src ++ PQM.mrest_own s.
Let W : list L5.range := PGS.W_srcG (op + PQM.OFF_SRC) ois src ++ Wx.

Hypothesis Hceil : hl_ceil L <= lo.
Hypothesis Hsp : sp <= lo.
Hypothesis Hscr : 0 <= scr.
Hypothesis Herr : hl_errno L + 4 <= lo.
Hypothesis Hlay : lo <= op /\ op + PQM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 64 /\ 0 <= lo.
Hypothesis Hdis : op + PQM.PSIZE <= ois \/ ois + 272 <= op.
Hypothesis HA : forall b, In b X -> apart (fst b) (snd b) lo (hi - lo) /\ (fst b + snd b <= hl_errno L \/ hl_errno L + 4 <= fst b)
                                   /\ 0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= 2 ^ 64.
Hypothesis HN : List.NoDup (map fst X).
Hypothesis HE : forall b1 b2, In b1 X -> In b2 X -> fst b1 <> fst b2 -> apart (fst b1) (snd b1) (fst b2) (snd b2).
Hypothesis HC : Forall (fun r => apart (fst r) (snd r) lo (hi - lo) /\ (forall b, In b (PQM.mrest_own s) -> apart (fst r) (snd r) (fst b) (snd b))) Wx.
Hypothesis HP : L5C.hpres L (X ++ LBX) sp scr W M M'.
Hypothesis HOW : PQM.mparser_at segs A T3 T4 vp M op ois (PQM.with_src s src).
Hypothesis HSRC : PM.src_fields_at segs T3 M' (op + PQM.OFF_SRC) ois (ois + 16) src'.
Hypothesis HQC : PM.sr_qc src' = PM.sr_qc src.

Lemma frame_client a : lo <= a < hi -> 0 <= a < 2 ^ 64 /\ client_addr L (X ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h04__x1h14__x2h24__x3h31Hh47__arithh54__ffh64__p1h74__p2h86__sat7h96__sat8h:8__varmaph;5__with<2Hah=4__x4h>1ah?2H1h@2H2hA2H3hB2H4hC2H5hD2H6hE2a0p;2p;1p;3p;5p;4p;7p;8p;6p-1R0p10000p4p710p9P0p100@bp4p710R1p8P0p10013R2p4p710p8P0P2p4p7210p8P0p1001Op4p710R2p8P0p10020R3p4p710p8P0P3p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R3p1004Ep4p710R0p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R4P1p8P4P0p8P4P3p8P4P2p8P4g007_R2p4p710p8P4p1008<p4p710p8p1008Yp4p7210P0p8g00A9j21Tg00AUj2FTg00B2j14Tg00BWj1ITg00C<j1@Tg00CZj2ZTg00D7R0j20Tg00DRj2UTP2j3QTg00E2j5=Tg00F4j2>Tg00;kj18Tg00G3j2BTg00GOj2gTg00H7j3cTg00H[j1GTg00I:j2?Tg00Icj3DTg00JLj2LTg00>9j1[Tg00=?j3CTg0096j1YTg00K8j1XTg00KVj2JTg00L4j1WTg00LRj1VTg00M=j2ETg00M`j2<Tg00NCj1TTg00Nej1STg00OCj3RTg00Ofj2tTg00PHj2sTg00Pbj2rTg00=_j3qTg00QNj3pTg00Qmj4oTg00R_j2nTg00S^j1lTg00T]j2HTg00U:j1jTg00V:j1iTg00W:j2fTg00:Tj2eTg00X@j3dTg00Xcj4KTg00Y>j3bTg00YXj3aTg00Z2j3hTg00ZUj1`Tg00[Tj4kTg00\2j4OTg00\]j7PTg00]Aj7_Tg00]ej8mTg00^Ij6]Tg00^mj6\Tf2R2f1R4f0R3'B'0p=2%43#4#4#4p=A%43#4p=^g00_QR1/13p=5g00<DR5P2P4P3Ckp=7P2g00_oR6g00`NR7P7g00`nR8P5P4g00aNP3COg00b5R9FPp=3P5P4g00bUP3COp=:P4P6P7P7P8P3P9FPp=;P2P6P7P7P8P4P3F_p=9f3R9P6P7P7P8P2P4P3Gmp=6P4P6P7P7P8P3E]p=MP4P6P7P7P8P3E\p=Np,2loR6/13p,2hiR:723p,4Hlayp,2opR;,16R<g00c<,F;/1:R;p,3oisR=,16R>g00d;R?#4R@#4RA#4RB#I#A#@,F=/1:R=%@@RC%4B#^RB#@RD'ZRE,1:RF%56RG'0RH'0RI'0RJ'0RK'0P0P<PK%59?29ERLp,1LRM1U55p,1Xp,3LBX3QRNp,2spROp,3scrRPP9D=1>M9#8'0'0P3P0P;PJf7RQ#5?2QEPMPNPOPPPQD=1>MQ#8'0'0P3P0P>PIf;RQ#5?2QEPMPNPOPPPQD=1>MQ#8'0'0P3P0P=PHf?RQ#5?2QEPMPNPOPPPQD=1>MQ#8'0'0P3P0PFPGfCR0#5?20EPMPNPOPPP0D=1>M0#8'0'0P3fFR0#51B0ERQ'0PMPNPOPPP0D=RR1>M0#8RS'01gCDRT1B1C%5D1B1E[[RU%5CRVg00d`RWAcCD4UW<RD%5E\W^<VRVg00e<RWg00ehRX#GRY#GRZ#GR[,?51?5Y1?5XRX5D5RY5D5g00fGR\'LR]%G[,?51?5ZRZ=D5X5D5/L\RX%[WR[5CW3C%YWR^%X5R_1J59R`?79_?72_774%W5Ra%V5Rb1E51Rc%I?,<5Rd53b%T7R7Pb%IA,<5Re1E5C%SB5R5RC53bRfP7Pb1<5?R?93bd1:?e,;b59bP7A3bc?1:?C,;b59bC6C6C61tb8R8P3P2g00g3Rcg00gSRg's1r32=qcgdAp514CoR1b5b:b;X05X15X25%54119ERg1192f4Rc722RhPL[[[^05^15^25P3P:P6fIRLP9PcfHRiO6b4b8b9PRPS1nN0%lMRN%4B#A#A#A#A#@RB'H/10/0QRQ1HOPRP/10?20O#8RR'0Rj%jM/10%iM7201fM0#8'0R0'ePQPRPTPUPDPVACW][9CWXP^1J521J5c?7c_?79_774PaPbPfP7Pb1<5@Rf93bd1:fe,;b59bP7Pb1E5B9d5?Re=3bdP7A3bef1:fC,;b59bC6C6C6P8P1b5b:b;X05X15X25X=51H2B/1c1H9B/1c?2cE[\h\g^05^15^25^=5P3P:P6PLPNPcPip,5HceilO7b4b8b9PTPUPDPVp-0RcAD5ZY/L\=CW[R[P^A7`2_R`97_4PaPb%I@,<5R@=3bdf5,MbRW59bP7PbA3b?@P7f6R@,MbR\1:d?,;b59b,NbC6C6P8P1b5b:b;X05X15X25X6cW71124/09Rd1149A2@92g00>YRZ[[[^05^15^25^6c^7cP311PL1BL:R:P6PLPOPip,3HspO7b4b8b9CK9bj03aPTPUPDPVP[P^A7`4_PaPb1<5ARa=3bf=9bWP7Pb%@ARA,E59h5?R?=3baP71:f?,;b99b\,NbC6C6P8P1b5b:b;X05X15X25X6cX7c1F4A/191F2A92@9PZ[[\d^05^15^25^6c^7cP3%`MRM/1LP:P6PLPMPip,4HerrO7b4b8b9PSeCKCKXDGXCFP4P3O2n2001000000121000000X3HXB=P4P3O2n2001000000121000000X3IXA>P4P3O2n2001000000121000000X3JX@;P4P3O2n2001000000121000000X3KX?<P4P3O2n2001000000121000000bEW<X>5P3O1X>5o"). Qed.
Lemma blk_client b a : In b X -> fst b <= a < fst b + snd b -> 0 <= a < 2 ^ 64 /\ client_addr L (X ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h04__x1h14__x2h24__x3h34__x4h41Hh52Hah61bh77__arithh84__ffh94__p1h:4__p2h;4__p3h<6__sat5h=6__sat6h>8__varmaph?5__with@4__x5hA4__x6hB4__x7hC1ahD2H0hE2H1hF2H2hG3HerhH3HinhI2_HhJ2a0p&0p;2p;3p;4p;1p;5p;7p;6p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R0p4p710R5p1004Ep4p710R6p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R7P2p8P7P6p8P7P5p8P7P3p8P7g007_R3p4p710p8P7p1008<p4p710p8p1008Yp4p7210P6p8g00DRk201TP1j3KTg00AUj26Tg00G3j23Tg00T]j2TTg00hQj4VTg00ZUj1aTg00A9j20Tg00B2j15Tg00C<j1GTg00:Tj2CTg00CZj2zTP3j3qTg00E2j5JTg00F4j2ITg00;kj1DTg00D7R3j2ETg00GOj2dTg00H7j3bTg00H[j1@Tg00I:j2WTg00JLj2NTg00>9j1`Tg00=?j3MTg0096j1_Tg00K8j1^Tg00KVj2HTg00L4j1]Tg00LRj1\Tg00BWj1FTg00Z2j3RTg00M=j2QTg00Nej1~Tg00OCj3}Tg00NCj1yTg00M`j2YTg00Ofj2vTg00PHj2uTg00Pbj2tTg00=_j3pTg00QNj3oTg00Qmj4nTg00R_j2lTg00S^j1kTg00U:j1jTg00V:j1iTg00W:j2mTg00Y>j3XTP0j5hTg00Xcj4STg00iRj4gTg00ilj7fTg00^mj6rTP4j3sTg00jPj3eTg00Icj3wTg00[Tj4xTg00\2j4ZTg00\]j7[Tg00]Aj7cTg00^Ij6{Tg00]ej8|Tg00<DR4f0R07s4p=2Ae440p=1f2R1f1R6'0/E0p=:%50#5p>00g00_QR7/06/E0p=41E60,E1p=<1070p=91616/00p=81W40p=?Aw460p=>P4P1P6P0Cxp=;1Y40p=BP1g00_oR5g00`NR2P2g00`nR8P4P6g00aNP0CZg00b5R9F[p=7P4P6g00bUP0CZp=PP6P5P2P2P8P0P9F[p=OP1P5P2P2P8P6P0Fcp==P6P5P2P2P8P0E{p=U%50#5#5#5p=Lf3R9P5P2P2P8P1P6P0G|p=A20144R:p,1XR;9K:6%21R<%11,6<,367:6p,2HAP9P6O2%29R<%19R=p,2loR>p,2hiR?/T>R@CV16<=RAp,1LRB#aRC'0g00d;RD#5RE#5RF#GRG,6CRH/0<'C%GERI%5FRJ#5$00RK#GRL'zRM,0A,4=,4<3<P3f4R<#2R=%1<RAP>P@CV16=ARN/0C10H='C%9=10NM,4A3<13<M,4<PBp,3LBXRA9q:;RNp,2spR=p,3scrROP<DJ1IB<#D3<P0f6RP#2%1PP>P@CVf7R@#2RQ%1@RR'6RS/0C10HQ'C%9Q10SM,4R3<P3f8RR#2RS%1RRQ'6RT/0C10HS'C10TM,4Q,4S13RM,4RPBPNP=POPRDJ1IBR#D3<P0f:RS#2RQ%1S;8C10HQ'Cf;RQ#2RH%1QRTA8HTM'4'4P3f<RT#2RH#9%1TRUA8HUM'413TM,4TPBPNP=POPTDJ1IBT#D3<P0f>#2#9f?RU#1RH%2U?8HM'4P3f@R3#1RH#9%23?8HM133M,43PBPNP=POP3DJ1IB3#D3<P0fBR3#1#9fCRH#2%1H;8M13HMRU,4HPBPNP=POPHDJRV1IBH#DRW'E1dILRX137I%9L137M[[RY%9IRZg00d`R[AbIL6UW5RL%9M\[^5ZRZp-0R[g00e<R\g00ehR]#@R^#@R_#@R`#@Ra#@Rb#@Rc#@Rd#@#?%?b1W4]R]'>'>g00fGRb'N%?d%?c/>]'>/Nb%`\Rc5M\3M%_\Rd%^4Ref5Rf,H41H4@7;97;@1H4<Rg1H4P7;@?;1e7;6%]4Rh%\4Ri%FDRj#5Rk#F#BRl%Fj#5#B5R4Rm1Q4I%~K5}4RI57i%y2RnPi1Q47Ro=7ilPnPi1Y4DRD97il1PDm,Oi5=iPnPif9,Ui1UiS%BjRj%FE#5#BRp57i%FJ#L#GRJ,Q49R4p%FF#BRF57iA7iFI1UiQ5=i5=i5=i5=i5=iPnPi%Bk1Q4GRk5R4=7ijPnA7ioD1PDI,Oi5=iCACACACACA1vi8RIP0P1g00g3Rog00gSRj'u1t01=pojdAo476CnR7b8b>b?X04X14X24X34X@4XA4XB4X9[X:[W;A8fPM%9P16@R,319:@116@JA:PMT7:P9:<@9<SQA8PGf13fM,4f[[[[[^04^14^24^34^@4^A4^B4^9[^:[^;[P0%9>p,2opR[g00c<;8?10>[fGR[#1Rf%2[R[p,3oisP?PCP>fFR>P9PRfDRRp,4Hlayp,4HerrO?b7b<b=PVPW1lNH%kB%5K#L#L#L#L#G'T?:HU1T=O13H=7:H#D'E%jB%iB,3H7:H1mBH#D'E'CP:AK:0N%20RB/0R%10,6B,3R3<X6:PRAK:RN%2RRN%1R,6N,3H7:HP:P;PAPRAK:R;AK:RA;X3DhfACSCg3XPXPYPLPZ%?aRa%?`/>]'>/Nb%?_%?^'>,>a/Nb=M\c5M\PdA;e<g9;e11H499;e<?;<e7;6PhPiPiP5P2P2P8A7imDAR4DkRk=7ilFfPnPi%BERE97il1PEm,Oi5=iPnPiP5P2P2P8A7iDE1PEk,Oi5=iErCACAPIP7b8b>b?X04X14X24X34A8190A80G1'C169<,319:91161G,399:19g00>Y[[[^04^14^24^34P0PfP[P>PCPTPRO6b7b<b=PWeCSCSWFWEP6P0O2n2001000000121000000W4WDP6P0O2n2001000000121000000W4WGP6P0O2n2001000000121000000W4WIP6P0O2n2001000000121000000bJW5WHXC4X6:P6P0O2XC4W6o"). Qed.
Lemma chunk_in : In (PM.sr_qc src, PM.CHUNK) X.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "p;2p;1p;4p;3p;5p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0p10020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R4p4p710R0p1004Ep4p710R5p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R6P2p8P6P5p8P6P0p8P6P3p8P6p1007_p4p710p8P6p1008<p4p710p8p1008Yp4p7210P5p8g00DRj2:Tg00jmj19Tg00kjj43Tg00>9j12Tg00=?j38Tg00lJj16TP1j30Tg00=_j34Tg00PHj25Tg00Y>j31TP4j57Tg00<DR4/:4R1P4P4p,3src#9g00mMC3R4%21R5581R6p,1s#6R3P4A0146A0143A4144A014515143131D7p,1X9014eo"). Qed.
Lemma rest_in b : In b (PQM.mrest_own s) -> In b X.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h01bh11Hp;2p;1p;3p;5p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0p10020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R4p4p710R0p1004Ep4p710R5p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R6P2p8P6P5p8P6P0p8P6P3p8P6p1007_p4p710p8P6p1008<p4p710p8p1008Yp4p7210P5p8g00DRj25Tg00lJj14TP1j30Tg00nJj11Tg00YXj33TP4j52Tg00<DR4/54R4f0R1p,1s#4R5504P4p,3src#1R6P5f1R3A0436A0435;31D2p,1X9043eW1X04P1O1W0o"). Qed.
Lemma wsrcf_in_frame r : In r (PGS.W_srcfG (op + PQM.OFF_SRC) ois) -> lo <= fst r /\ fst r + snd r <= hi.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h01Hh14__p1h24__x1h34__x2h44__x3h54__p2h64__p3h77__arithh84__ffh96__sat7h:6__sat8h;8__varmaph<5__with=1rh>2Hah?2H1h@2H2hA2H3hB2H4hC2H5hD2H6hE1ap;2p;1p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0g004ER5p4p710R6p8p1004ap6067111111004p1005^p4p771111110p8g006cR7p4p70R8P2p8P8P6p8P8P0p8P8P3p8P8p1007_p4p710p8P8p1008<p4p710p8p1008Yp4p7210P6p8g00A9j23Tg00B2j18Tg00BWj1=Tg00C<j16Tg00CZj2XTg00D7R6j25Tg00AUj21Tg00oIj2OTg00DRj2eTg00>9j1JTg00=?j3DTg00GOj2YTg00G3j2ITg00H7j3WTg0096j1VTg00KVj2HTg00[Tj4TTg00L4j1STg00LRj1RTg00M`j2ATg00NCj1NTg00Ofj2MTg00PHj2PTg00Pbj2QTg00=_j3GTg00QNj3LTg00Qmj4UTP5j6BTP1j3dTP4j3cTg00jPj3bTg00kjj4`Tg00\2j4_Tg00\]j7]Tg00M=j2\Tg00Z2j3[Tg00^Ij6^Tg00]Aj7ZTg00]ej8aTf2R4f1R1'1f0R5'3p=C%85#8p=:Ad715p=4g00<DR8?c85p=2f4R3f3R0'3Ab881,14/35'5p=0P8P8P1P5C`p=EAG715p=>P4g00_oR2g00`NR9P9g00`nR:P8P1g00aNP5C_g00b5F]p=;1\85p=<A[815p=7P1P2P9P9P:P5E^p=@P4P2P9P9P:P1P5FZp=9P0P2P9P9P:P4P1P5Gap=?1341/55p=K13301141/35'5p=Fp,4HlayR2p,2loR;p,2opR<'3R=g00c<p,2hiR>5C<R?p,3oisR@,3;RAg00d;RB#8RC#8RD#8RE#=#:#:#6RF=C@>RG%6CRH%8E#:RI#6RJ'XRK,3>RLg00_QRM/3;RN'5RO'5RP'5RQ'5RR'5P6P=PRg010G,1</O@RS,44P;%20RTPTP0P>D0[P5P6P?PQf6RT/4SP;f7RU#2RVPVPUP>D0[P5P6PAPPf:/4SP;f;RV#2RWPWPVP>D0[P5P6PGPOf>/4SP;f?RV#2RWPWPVP>D0[P5P6PLPNfB/4SP;fCR6#2RVPVP6P>D0[P5fER61e88RV%=BRW#:RX#8#6RY,1<%:I#6RI'1%=C#8#:#6RZ'ER[11@Z%6ERE'ER\%=D#=#8#:#6R],1@%6DRD'ER^%JVR_5DVR`5DVRV3D'4g00:TRafFRb,>[14bVP;fGRc#2RdPdPcP>D0P51>[cP7P[P;%25RdPdP5P>D0X=7Rd1YHJRe1IMH13MJ1IMK[[Rf13MHRgg00d`RhAWHJ1UW>RJ13MK\h^>gRgp-0Rhg00e<RK#JRH%VKRKP81H84P11H80CTRi%S8Rj%R8Rk1A8BRB1A8CRC5;kRl%=X#:#:#6RX#<,7C1A8WRW5;kf5Rm,@kRn59k59k%N9R9%<Y,7C%<I'7Ro9;kB%<ZRp,7o=;kW59kC?1Mk:R:P5P4g00g3Rog00gSRq'P1Q54=GoqdAL8M1CURMb8b;b<X28X38X48W11351Rq111X?K40'5P1114Y/1IRIPIPZP0DF[^28^38^48^1hP5PQP>P<P;P2O5b7b9b:P;%2[RIPIP[P>D0efHR[P5EBW0P5O114cVPa1>\[14[`P;fIR[#2RcPcP[P>D0P51>\[P7P\PdPePfPJPgPHPKPiPjPk1@kT%<F,7C=;kW1@kU59k99kl59k99knRnP917CpRp9;kB%<E,7p=;kW59kC?P:PMb8b;b<X28X38X48X1hX5hX6h111F?K4m,5q,53,50R3P1114ZRZPZPEP0DF[^28^38^48^1h^5h^6hP5POAC<X>P=P>P@P;P2O7R2b7b9b:P;%2\R@P@P\P>D0efJR\P5EBW0P5O114[`Pa1>^\14\_P;fKR\#2RaPaP\P>D0P51>^\P7P^PdPePfPJPgPHPKPiPjPkPnP9%<],7CRC9;kB%<D,7C=;kW59kC?P:PMb8b;b<X28X38X48X1hX5hX6hP1114]R]P]PDP0DF\3^28^38^48^1h^5h^6hP2b7b9b:P;%2^R2P2P^P>D0efLP5EBW0P5O114\_g00>YP;fMR\#2R_P_P\P>D0P5n010000000W0P5O1n200100000021100010000W0P5O1n200100000021100011000W0P5O1n200100000021100011000W0146SP;%2bR;P;PbP>D0[eXDNXCLP1P5O2n2001000000121000000X0OXBGP1P5O2n2001000000121000000X0PXAAP1P5O2n2001000000121000000X0QX@?P1P5O2n2001000000121000000X0RX?=P1P5O2n2001000000121000000bEX=7P5O1X=7o"). Qed.

(* [comment removed for export] *)
Definition named (a : Z) : Prop := op <= a < op + PQM.PSIZE /\ ~ (op + 280 <= a < op + 320).

Lemma named_kept a : named a -> L5C.kept L (X ++ LBX) sp scr W a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h01Hh14__x1h24__x2h34__x3h42Hrh51rh67__arithh76__sat7h86__sat8h92H0h:4__ffh;8__varmaph<5__with=4__x4h>4__x5h?2Hah@2a0hA1bhB3HaphC2_HhD4__x6hE4__x7hF1ahG1ChH1EhI2H1hJ2H2hK2H3hL2H4hM2H5hN2H6hO3Hr'hP2HshQ1Rp%0p&0p;1p;2p;3p;6p;4p;5p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0g004ER5p4p710R6p8p1004ap6067111111004p1005^p4p771111110p8g006cR7p4p70R8P2p8P8P6p8P8P0p8P8P3p8P8g007_R3p4p710p8P8g011HR8p4p710p8p1008Yp4p7210P6p8g011hk10ETg00AUj20Tg00G3j26Tg00B2j1?Tg00BWj1JTg00C<j1:Tg00DRj2{TP3j3nTg012ij6GTg00A9j23Tg00CZk20DTg00D7R3j21Tg00GOk20?Tg00H7k30;Tg00H[j1CTg00I:j2jTg00>9j1gTg0096j1|Tg00K8j1yTg00L4j1wTg00LRj1uTg00NCj1sTg00M`j2cTg00Ofk20CTg00PHk20BTg00Pbk20ATg00=_j3pTg00QNk30>Tg00Qmk40<Tg00:TS00j2XTg013ek20:Tg00E2j5STg00F4j2RTg00;kj1;Tg009Vj2kTg00oIk206Tg00jmk105Tg00kjj4lTg00=?j3UTP5j7`Tg00:nj2\Tg00T]j2hTg00hQj4LTg00ZUk103Tg00X@k302Tg014mk100Tg0164j5~Tg017<j5eTg00lJj1}TP1j3fTP8k601Tg018Cj3zTg00Xcj4bTg00Icj3]Tg00JLj2oTg00KVk207Tg00[Tk408Tg00M=j2xTg00Z2k309Tg00\2j4WTg00\]j7YTg00]Aj7mTg00^mj6vTg00ilk70=Tg00]ej8^TP4k30@Tg00jPj3tTf2R4f1R8'3f0R1'1p=d%?1#?p==f3R5/341681'1#;p=I1048/31p=8g00_QR6/31p=4g00<DR0/j1p=FA]081p=OA]081g00fGR2'op=EA]0819]04p=ig00e<R9AU9817U4p=B20701p=TP0P4P8P1H08p=51c01p=N1x01p=AB09081p=2P0P8g00aNR:P1CWp=Kf6R;g00_oR<g00`NR=P=g00`nR>f5R?P<P=P=P>P0f4R@P:P5CWg00b5RAFYP4P<P=P=P>P0P8g00bURBP1CWPAFYFmp=HP8P<P=P=P>P1Evp=PP4P<P=P=P>P0P8P:P1CWPAFYp=DP4P<P=P=P>P8P1K0=p=_P0P8PBP1CWp=rP5P<P=P=P>P4P8P<P=P=P>P1PAFYFmp=qP5P<P=P=P>P4P8P1G^p=[P;P<P=P=P>P?P@P5P<P=P=P>P4P8P1G^G^p=ZP@P<P=P=P>P5P<P=P=P>P4PAFYP8P1G^p=M13@51081,64'1p=<1681,14p=VAf781p=>P0P0P8P1Clp=aAp781p=QB0@001p=9At001p=713@51081,64'1#;p=@1o12p>04&0E1P3p,2opR2g00c<,02RA,687d8g00d;R<#?RB#?R:#?RC#JRD#J#?#=#:RE,02RFP8P8%JBS01#?S02#=RG#?#=#:RH,02RICIp,1LRJ1{00RKp,1Xp,3LBX3nRLp,2spRMp,3scrRNp,1WROP4EGP1165A9d25PFP@P@PICIp,4Hlayp,2loRI/32S03p,2hiRF,3AS04p,3oisRA,3IS05%=D#=#:RD=8AFS06%:BRP%?C#=RQ#:RR+0DRS,3FS07%4IS08'1S09'1S0:'1S0;'1S0<'1P3Q03Q0<PJPLPMPNPOf7RTEGP1Q03Q0<P3Q04Q0;PJPLPMPNPOf;S0=EGP1Q04Q0;P3Q05Q0:PJPLPMPNPOf?S0>EGP1Q05Q0:P3Q06Q09PJPLPMPNPOfCEGP1Q06Q09P3Q07Q08PJPLPMPNPOfGEGP1Q07Q08fJRU20?PRRV166P%4R166S[[RW%4PRXg00d`RYB0;PR8UW?RR%4S\Y^?XRXg00ehRY#CRP#CRZ#CR[#CR\#CR]#FR^%F\R\1j0YRY'OS0?'E%C]R]#FS0@%FZS0A/OYRZ'ER_%C]S0B#FS0C%FPS0D=i\Y'E%F[R[/OY,E^RY%g9RP9B_Y7B_5B_3B%|9S0E%T@%y0R975??549%T?S0F?5?9?559758%w0S0G%u0R_P_%J:RY#NR]%ADS0H'2R`%J<Ra#NRb'K%s=R=P_P_1c0<R</K]P=P_P_%NCRc%=aRa#J#=#=#:Rd#AS0I'2Re/KbP=P_P_1K<cP=P_P_P_%AERf,2c%NBRBP_PB%AHRg,2cFH,P_S0JP=P_P_P_PcPBP_PBPeFHS0KP=P_AD_e]AD_`c5__P=P_AD_<BS0LP_1rBbCqC[FZDMDMDMDM20C_>R>P1P4g00g3R`g00gSRh+0B20A14=p`hdB0>068H0<R6b:b;b<X10X20X30X=0X>0A8@D4138?A8?d@135;10TEP?P?PTPHD<g00>YRh[f8R`P;P;P`PdD<f9Rif:Rj78dA8jDi'X13T`S0M?V`i[[[[[[[^10^20^30^=0^>0P1PAP2PFfMRkPIP`f<Rlf@fDfHfIp,4HdisS0NO<b6b7b8+0:%4U?VUSPJPLPMPNPUDS1RJU#;'1'1P3fKRm#4?VmSPJPLPMPNPmDS1RJm#;'1PJPLPMPNPOfLEGP1%4k?VkSPJPLPMPNfNS0ODSQ0O,RJ#;'1P3PJPLPMPNfOS0PDSQ0P,RJ#;PJPLPMPNPOfPEGP1PJPLPMPNfQDSfRS0Q,RJ#;fSRk#4?VkSPJPLPMPNPkDSRn1RJk#;Ro1kOkS0R'1Rp'1P?PnPpP8PoQ0RP1g010G,02006ARoP0P0p,3src$05Rpg00mMS0SClRn%gKRq5UKRr5n7p,2WxS0TPkPoPrPk1>1oRrP11>8oQ00%?a#:Ra,02%=Q#:RQ'0Rs%:GRG'aRt/Q410AGS0U%:CRC'aRu%JY#?#=#:RY,0AS0V%::R:'aRv=UKqRw5UKS0W,>4%95S0XfWS0YQ0YQ0X%75S0ZD@P11Qt5P7Pt%98RxfZRyPy%78Rz,0xS0[CI^4rX571>toPVPWPRPXP3f[R{#4S0\16{SS0]Psf\R|P|PsPGD@f=Rsf]R}#4S0^f^R~/6SS0_PPQ0E%T4?589Q0GP_P_P_12<fPBP_PB12<gFH,P_P=P_P_%Aa,2<%AQ'2S0`PBP_PBQ0`%AGS0a'2FH,P_C[P>P6b:b;b<X10X20101EP8P8P1PHD<Ph[108a/0QRQP4P4PQPGD<Ph[[^10^20P1f`RQP2P{O3b6W9W0P8P1O2n2001000000121000000b7b8%9tS0`fYRaPaQ0`%7tD@eW4P@P1P5F`W0P1O1Q0W,>5Q001Qu@1>@w%9?RtPaPaPt%7?D@P11Qu?P7PuPxP|P|Q0[CI^4rX571>uoPVPWPRPXP3Q0^16}SS0WQ0UP~P~Q0UPCD@Q0>f_Rt#4S0>16QSQ0AQ0D'O,E[S0A1E^Z1O\ZRZ$04Q0A;BP3BS0AQ0E%T5?559?549?589S0UQ0GP_Q0JP=P_Q0KP=P_AD_e<Q0H,2<=D_c5__RcP=P_P_Q0a,2<RePBP_PB%AC,2eFH,P_C[FZP>P6b:b;b<X10X20X30104EP8P8P4PHD<Ph[ReP5P4P4P5PdD<R\A8@d4A84D@'XR^105GRGP@P@PGPCD<Ph[[[[^10^20^30P1P2fbRCPAP}P~Q0NO6b6W9W0P8P1O2n2001000000121000000b7b8%9uRGP{P{PG%7uD@eW4P;P1P?F`W0P1O11>?wQ001Qv;1>;q%9TRwP{P{Pw%7TD@P11QvTP7PvPxP~P~Q0[CI^4rX571>voPVPWPRPXP3Q0>16tSQ0VPQPQQ0VP:D@fAfa#416CSQ0AQ0EQ0UQ0GP_Q0JP=P_Q0KP=P_PcP=P_P_%AY,2<RcPBP_PB%A:,2cFH,P_C[FZP>P6b:b;b<X10X20X30105YRYP@P@PYP:D<Ph[\^\\\e^10^20^30P1P2fdPAPtPQQ0NO6b6W9W0P8P1O2n2001000000121000000b7b8%9vReP}P}Pe%7vD@eW4P`P1PTF`W0P1O11>TqPh%9iRvP}P}Pv%7iD@P1n010000000W0P1O1n200100000021100010000W0P1O1n200100000021100011000W0P1O1n200100000021100011000fVRv,\4#;R}ebOW4X571kokePnPqPkp,2HAPng019MO2%9nRq%7nRoPI1hFIReCLR\10qoR^&03JRY'3A8Y:q'X%4q%4o13^S'1'1'1Ro'1P3P\PoPpfURYPYQ0S,0pRYCIP1PVPWPRPXP3%4y16ySPpP{P{PYCIPl%4|Q0WQ0B#CRY#C#C#FRSQ0CQ0D7i['ER[Q0@Q0?'O,ESR:%FY/OZ,ESRSABS:P3B9B[[7B[Q0E%T;?5T99594Q0F?5@9%TT?5T9755758Q0GP_12<bRbQ01#NR95D_Q02#NR@>0209,29=D_<5__P=P_Q01#J#NR<Q0H'2R[=D_@P=P_P_1K9<P=P_P_Q0I,2]RS/K@P=P_P_1K9]P=P_P_P_12]fPBP_PB12]gFH,P_P=P_P_P_P]PBP_PBPSFHP=P_AD_S<AD_[]5__P=P_Q0LP_1rBbCq,P_C[FZDMDMDMFZP>P6b:b;b<X10X20X30X=0X>0XD0XE0R6A81451h?5=851'XA8TD;13?`A8Td`Q0M10iEP;P;PiPHD<Ph[PjPTPTPjPdD<Q0=?8dsQ0=98sD'XP`PiPiP`PjD<Ph[[[[[[[[[^10^20^30^=0^>0^D0^E0RhP1PAPFP2PIQ0SPtPpP`PUQ0OQ0QPvPyP{Q0NO?b6W9W0P8P1O2n2001000000121000000b7b8XCoXB\P8P1O2n2001000000121000000b@PqPkPkP^CIe1\nk#;e&00kD~DeQ0TP7%91%71PIPeCLp,1s#}9fK1Rn%94%74PxPzCL[^AK'1X5KR4fT,\1#;X57P4P1O1P3PxPzPIPeCLQ0XQ0ZPxPzCL\n^AKP}P1Q0XQ0ZPIPeCL%9;%7;PxPzCL\n^AKPVPWPRPXP3Q0\Q0]%9`R3P|P|P3%7`D@PsQ0^Q0_P6PhP1PAPFP2PI%7lPQ%9lP`PmQ0PPkQ0YP{P|Q0NO?b6W9W0P8P1O2n2001000000121000000b7b81\?a#;eWCWBP8P1O2n2001000000121000000W0X57Q0Tp,2HCJ017zkDeQ0ReCbCbCbWHWGP8P1O2n2001000000121000000W0WQP8P1O2n2001000000121000000b@PJPLPMPNPOPUEGeWNWMP8P1O2n2001000000121000000W0WLP8P1O2n2001000000121000000W0WKP8P1O2n2001000000121000000W0WJP8P1O2n2001000000121000000W0WIP8P1O2n2001000000121000000b@WPW?P8P1O2n2001000000121000000W0XF0P1O1XF0o"). Qed.
Lemma named_ag a0 n : (forall a, a0 <= a < a0 + n -> named a) -> L5C.agree_on M M' a0 n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h01ah12a0h21nh33HN'h42Hap;2p;1p;3p;:p;4p-1R0p10000p4p710p9P0p100@bp4p710R1p8P0p10013R2p4p710p8P0P2p4p7210p8P0p1001Op4p710R2p8P0p10020R3p4p710p8P0P3p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R3p1004Ep4p710R0p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R4P1p8P4P0p8P4P3p8P4P2p8P4g007_R2p4p710p8P4p1008<p4p710p8p1008Yp4p7210P0p8g00A9j20Tg00AUj23Tg00G3j22Tg00D7j21Tg011hj19Tg00DRj28TP2j37Tg01:Qj24Tg01;Wl:5Tg01<Yj46Tg00<DR2f2R0f0R4'0f1R3,30,24'1%93[^02f3R1/041310,24'1p,1L1822p,1Xp,3LBX37p,2spp,3scrp,1Wp,1MR1p,2M'R5P3p,2HPP0P3P4O2,43M:5W4X02P1P5P0P3C6eW3X22X12P3P4O2X22W1o"). Qed.

Lemma stk_in : In (PQM.p_sb s, PQM.PSZ * 2 ^ PQM.p_sk s) X.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "p;1p;2p;4p;3p;5p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0p10020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R4p4p710R0p1004Ep4p710R5p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R6P2p8P6P5p8P6P0p8P6P3p8P6g007_R3p4p710p8P6p1008<p4p710p8p1008Yp4p7210P5p8g01=Yj1ETg00B2j1DTg00C<j13Tg01>Wj12Tg00CZj2CTg01?Uj2;Tg00kjj4:Tg00DRj24Tg00>9j15Tg00=?j36Tg01@2j17Tg01A0j18Tg01Amj19Tg01Bkj1BTP3j3>TP1j30Tg00=_j3<Tg00PHj2=Tg00Y>j31TP4j5?Tg00lJj1@Tg01Cij2ATg00<DR4P4p,1sR1#Eg01Dlg00d;#D#3%21'C';C:R31444R4%54R59643R6%71#8%91#B5>4R0P3A0436A0430A<433A04351=433131D?%@19043e'Ao"). Qed.
Lemma stk_kept a : PQM.p_sb s <= a < PQM.p_sb s + PQM.PSZ * 2 ^ PQM.p_sk s -> L5C.kept L (X ++ LBX) sp scr W a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "p'0h01Hh14__x1h24__x2h34__x3h44__x4h54__x5h64__x6h71ah82Hah91li001lh:1rh;2H0h<7__arithh=4__ffh>6__sat5h?6__sat6h@6__sat7hA6__sat8hB8__varmaphC5__withD1bi011bhE1AhF3HaphG2_HhH4__x7hI4__x8hJ2a0hK1ChL1EhM2E0hN2F1hO2F2hP2H'hQ2HNhR2HQhS4HapbhT4HapfhU2HrhV2NIhW1Ri022Ini032l'p%0p&0p;1p;2p;4p;3p;5p;6p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0g0013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R4p8P0g0020R5p4p710p8P0P5p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0p1004Ep4p710R6p8p1004ap6067111111004p1005^p4p771111110p8g006cR7p4p70R8P2p8P8P6p8P8P0p8P8P4p8P8g007_R4p4p710p8P8g011HR8p4p710p8p1008Yp4p7210P6p8g01=Yk10CTg00B2j1?Tg00C<j1UTg01>Wj1vTg00CZj2jTg01?Uj2KTg00kjj4`Tg01Eik402Tg00DRj2qTP4j3TTg00E2j5LTg00F4j2JTg00;kj10Tg00D7R4j21Tg012ij6eTg009Vj2RTg00T]j2bTg00hQj49Tg00AUj26Tg00ZUk103Tg00A9j22Tg00:Tj2QTg0096S00j1XTg00=?j3MTg01FoR6j2BTP1j3ATg01GKj3uTg00jmj1sTP5j2rj3xTg01@2j1pTg01A0j1oTg01Amj1nTg01Bkj1mTP3j4lTg00=_j3DTg01Gnk40BTg00Y>j3kTg00oIk20ATg00>9j1iTg01HJk20@Tg00:nj2ITg00GOj2gTg00G3j2:Tg00H7j3fTg00H[j1HTg00I:j2dTg00KVj2NTg00K8k10;Tg00L4k109Tg00LRk108Tg00M`j2cTg00BWj1CTg00Z2j3OTg00NCk105Tg01ITj3aTg00X@k304Tg00Ofk201Tg00PHj2]Tg00Pbk200Tg00QNj3}Tg00Qmj4|Tg00\2j4YTg014mj1{Tg0164j5~Tg017<j5_Tg00lJj1zTP8j6yTg018Ck306Tg00Xcj4[Tg00jPk307Tg00Icj3wTg00JLk20:Tg00[Tj4\Tg00\]j7hTg00ilj7tTg00]Ak70<Tg00^mk60=Tg00]ek80>Tf4R8f3R3'2f2R5f1R1f0R0'6':'1p=8g00_QR2/20p=31:10,15p=Sg00<DR9?x90p=5B07990p=71251/10p>0?1d90p=EAw910p=;g00fG-0:0p=Gg00e<R:?M10p=<P9P9P8P3P5C\P1P0C\p=@P9P5P1P0C\p=F1c90p==P5g00_oR;g00`NR<P<g00`nR=P9P1g00aNP0CYg00b5R>Fhp=4P5P;P<P<P=P1P0Ftp=ZP9P1g00bUP0CYp=VP1P;P<P<P=P0P>Fhp=PP5P;P<P<P=P1P0K0<p=WP1P;P<P<P=P0J0=p=^P3P;P<P<P=P5P1P0L0>p=>p,1sR;$0CR>P0P0P>g01DlR?g00d;R@#?RA#URB%v;RC'jRD'KRED8P9P9P>PEC`REP1g01J7RFP0H02%31%?ARG#?RH#?RI#?#?#URJ,jBRK7S1p,1LRL1q99RMp,1Xp,3LBX3TRNp,2spROp,3scrRPP1DL1JL1#0'1'1P4%35?S5KPLPNPOPPP5DL1JL5#0'1PLPNPOPPp,1WRQP3EeP0%38?S8KPLPNPOPPf5RRDL1JLR#0'1P4PLPNPOPPf6RSDL1JLS#0PLPNPOPPPQf7RTEeP0PLPNPOPPf8RUDLf9RV,JL#0f:RW#3?SWKPLPNPOPPPWDLRP1JLW#0RO1RQWRN'1RX'1PRPPPXP1POPNP0p,2HAPEPFO2%5ERN%7EROp,2loRXp,2hiRP/bXRYC9RZ16NOR[&03LRL'2%UG,6L/2N'Q%3N%3O12[K'1'1'1R['1P4PZP[f<,RQP0P6p4p710R6%X1RLP4AM510,B5AA351#01B31'1[RGAA510#01B50'1AM351,B3R\[AA835#01B85'1\\Au510P1n2001000000120000000W9X70WEPG^9L^70^E6P0P9P9P9p,3src#sR6g00mMRLC`RG#5R\PMP91r99%p;#o%n;#m5TMS01ClR]9M9NR^p,2HNO4AA9\^#0R_1B9^R^'1P4P_P^AD96>R`#0RaP0P5AD9N\AA9\]P9P\PNP0H0B3kO1XM`PaeXG^XV_P1P0O2n2001000000120000000bQb0Pap,2opg010G'6p,3ois+0ARa%iMR_9MMGR^5T7p,2WxR`f@R]PaP^P]AA70a20@10%51R^%71Rb,6^/2P60?XP4%55Rc,2X%75S02,6c/2PfD,I3#0P0%58,2X%5RS03%7RS04'6/2P1gBCRd1:2BRe%3C1:2D[[Rf%3BRgg00d`RhAfBC1UW8RC%3D\h^8gRi1gBJRj%3J1:2K[\eReAfBJ1VhX8gRJ%3K\h^8gRgP4fKRh#3S051:hKS06f;Rh#5RBfLRkPkPB%7hD8#0S07fFRhfM#3RBfN/:KRkg00ehRl#HRm#HRn#HRo#HRp#HRq#H#E%EpRp%Eo1d9l';Rl';Ro';#G%EqRq%En%Em';Rm,;pRp';#G%i:Rn'<'<%X:R:1N9TPU&0;9RrPUPrD@P5PrP11N9U?FUrP8PrP31N9RRs1N9SRt7FUD@D@&099Ru&089Rv1c9@Rw%C@R@#=5O9Rx%CARy#C#=Rz54v&05<R<Pv%=yRy=4vwP<Pv%C@R@#C#=R{%=IRI%CH#=5a95O9RH=4vyB049zy9O9y=4v{5ZvP<Pv%=ARA94v{1VAH,Pv5WvP<A4vwA1VAx,Pv5Wv,^vRyC>S08C>C>C>201v=R=P0P5g00g3Rzg00gSR|']20005=Dz|dA}921C|R2b=bBbCX19X29X39X49X59X69XH9XI91605R|/2812811KUV,6T/2R1bSR,6R/2T'QPUP8P8PU1KVWD8P8PRPRP8PSD8g00>YRU[[[[[^19^29^39^49^59^69^H9^I9P0PDP?P>PPPXf?RP#7S09fPRz%5PRPPVPWfBfOR}O<b<W;W0P1P0O2n2001000000121000000b>b?b@bAfGR~,IS#0eWOWNP1P0O2n2001000000121000000b0WUX:71Ra]ePGP_P]p,2HEPGPEg019MPFP0O5P\%7GRFPNPOC9PdPfPCPiPjPePJPgP4fER_#31:_KP6PhPhP6PLD8#0P]%3~fH/:K1;qm#GRm1;ql#GRq1<qn'<,<m'<P:PtPSPrPSPrD@RtP51N989FrSRmP1AFrSs9Fr3D@PuPv%?@#=R@94vxAa9{I9O9@RI=4vw5ZvP<PvP9Pwg01K9P@CY,Pv,^vP<PvA4v@A1VAI,Pv5WvP<PyC>C>C>P=P2b=bBbCX19X29X39X49X59X6912|31K8R,63/20'QR|AD918PU[PRP3P3PR1KSTD8P3P8P8P3PRD8PU[[[[^19^29^39^49^59^69P0PDP?P>PLfJP6PVPWfIO9b<W;W0P1P0O2n2001000000121000000b>b?b@bAbFP\P]P]P\PFD8#0e1IG]#0e%{]D~D_P7%50%70PXPYC9%z;9AM0R;PcQ02P^PbC9[^DM'1X:MRcfA,I0#0X:7PcP0O1P4P^PbPXPYC9%53Rc%73RGP^PbC9\;^DMfC,I5#0P0PcPGPXPYC9%5S%7SP^PbC9\;^DMP0PEADMEE%XMR;p-0Rb]9^7MQ00PMPbP0PUADM13P8P3P0O2'Qn10110000020020101103X9;X7Mp?1001102PEQ01O21]ME3kO2Q03Q04PNPOC9PdPfPCPiPjPePJPgP4Q05Q06Q07Ph%Gp%Go/<n'<P:PsPSPrPSPrD@P5PrP1AFt3mD@PuPvA4vx{A4vHw5ZvP<Q08C>P=P2b=bBbCX19X29X39X49X59X69P8P5P5P81KRSD8P5P3P3P5P8D8PU[[\|^19^29^39^49^59^69P0PDP?P>Q09PzPPPVP}O8b<X;kX0BP1P0O2n2001000000121000000b>b?b@bAbP1IRh#0eWSWFP1P0O2n2001000000121000000W0X:7P`p,2HCEy:06`]D_1RQ]ebRXG[XTZP1P0O2n2001000000121000000bJC[C[C[WLWKP1P0O2n2001000000121000000W0WWP1P0O2n2001000000121000000bJW8X79P0O1X79o"). Qed.

Lemma blk_dkr b : In b X -> PQMF.dkr M M' (fst b) (snd b).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h01bh11Ch21Dh31Eh41Hh52Hah63Hinh71Rh81ah92a0p;2p;3p;1p;4p;5p;=p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0p1004Ep4p710R5p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R6P2p8P6P5p8P6P0p8P6P3p8P6g007_R3p4p710p8P6p1008<p4p710p8p1008Yp4p7210P5p8g00DRj2GTP1j3FTP4j3;Tg00A9j25Tg00jPj3<Tg00AUj2DTg00G3j26Tg00D7R4j20Tg00B2j12Tg00Nej19Tg01K`j1>Tg01LCj1=Tg01Lej27Tg00NCj1ETg00=_j38Tg00;kj11Tg01Eij4CTg00C<j1:Tg00CZj2BTP3j3ATg00E2j53Tg00F4j24Tg01MKl=@Tg01NMj4?Tg00<DR3/G3R1f0R5p,1XR65F1f2R09;33R2/55A<330,D2,65'0g00d;#2R2#2#2R7#9#>R8#=R9p,1MR:%27#2#2R7#9R;f1R<'7O1%E8R838#1f4R=P0f3R>P<CCg00_QR?/50%:2%:7'BR7,60'0p,1LR2p,3LBX9A16R6p,2spR@p,3scrRAP0D31420#1'0'0P415?>16>7'0P2P6P@PAP>D3142>#1'0p,2M'R>17;=O1=898#1P5f5R=,5?16=7'0P2P6P@PAf6R7D31427#1'0P4P2P6P@PAf7R4D31424#1P>f8,7;O1=898#1P5P2P6P@PAf9R8D3f:,42#1P2P6P@PAp,1WP:P>f;p,2HPP=P<P5P8M=@W3W1P<P5O2n2001000000120000000W4W7P<P5O2n2001000000120000000b9W2W5X83P:P>A;33<A<33<C?eW6X01P5O1W0o"). Qed.
Lemma frame_dkr : PQMF.dkr M M' op PQM.PSIZE.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "h01Hh12Hah24__x1h34__x2h44__x3h54__x4h64__x5h74__x6h82a0h91Ch:1Dh;1Eh<2H1h=2H2h>2H3h?2H4h@2H5hA2H6hB1RhC7__arithhD4__ffhE6__sat7hF6__sat8hG8__varmaphH5__withI1ap;2p;1p;3p;4p;7p;5p;=p;8p-1R0p10000p4p710p9P0p100@bp4p710R1p8P0p10013R2p4p710p8P0P2p4p7210p8P0p1001Op4p710R2p8P0p10020R3p4p710p8P0P3p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R3p1004Ep4p710R0p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R4P1p8P4P0p8P4P3p8P4P2p8P4g007_R2p4p710p8P4p1008<p4p710p8p1008Yp4p7210P0p8g00A9j20Tg00AUj29Tg00G3j24Tg00D7R0j21Tg00B2j12Tg00Nej1MTg01K`j1ZTg01LCj1XTg01Lej25Tg00NCj1KTg00BWj1BTg00C<j1FTg00CZj2jTg00GOj2cTg00H7j3]Tg00H[j1?Tg00I:j2NTg00JLj2GTg00>9j1WTg00=?j3CTg0096j1VTg00KVj2ETg00K8j1UTg00L4j1STg00LRj1RTg00M`j2>Tg00M=j2QTg00Z2j3ITg00\2j4DTg00ilj7PTg00Ofj2TTg00PHj2iTg00Pbj2hTg00=_j3OTg00QNj3gTg00Qmj4fTg00:Tj2eTg013ej2bTg00DRj2_TP2j3^Tg00E2j5ATg00F4j2@Tg00;kj1=Tg01MKl=\Tg01NMj4`Tg00Icj3aTg00[Tj4[Tg00\]j7LTg00]Aj7dTg00]ej8YTf2R2f1R4f0R33O#=p=3g00_QR1/03p=8g00<DR5/N3p=<Aa543p=7P5P2P4P3C[p=:P2g00_oR6g00`NR7P7g00`nR8P5P4g00aNP3CDg00b5R9FLp=6P4P6P7P7P8P3P9FLp=HP2P6P7P7P8P4P3Fdp=Jf3R9P6P7P7P8P2P4P3GYp=;p,2opR:/03g00c<R;,9:R<,43'1g00d;R=#2R>#2R?#2R@#M#ZRA#XRBp,1MRC%2@#2#2RD#MRE/54O1%KARA33p,4Hlayp,2loRF/0:RGp,2hiRH,0<R<p,3oisRI,0FRJ%B@#2#2#2#2#FRK,9I/0HRL%F>RM%FDRD'jRN,0HRO%8FRP'1RQ'1RR'1RS'1RT'1P0PGPTp,2M'RUf4RV,5EO1=3BAP3P0P<PSPUf8RW,5EO1=3BAP3P0PJPRPUf<RX,5EO1=3BAP3P0PLPQPUf@RY,5EO1=3BAP3P0POPPPUfDRZ,5EO1=3BAP3fGR[1cMD141M%8D141N[[%8MR\g00d`R]A]MD4UW1%8N\]^1\g00e<R\g00ehR]#?RD#?RM#?R^#?R_#<%<^R^1N5]R]'7'7g00fGR`'G%?_R_#<%<M/7]'7/G`RM%?_#<%<D/7],7^'7/G`%W\5C\9C\M5C\3C%V\1E5Vf6R\%U5RM3:1E5\?:\M7:2f5R`,E5?:\M?:9M7:4%S5%R5RM%B>#2,>5R^1Q5K5I5R]%B=,>5RD56M%K7R_PM1>5=R==6M^P_PM1>5@R@%B?,>55I5R?=6MDP_PMA6M=@P_PM1>5>R>96M@P5P>g00bURaP?CD,HM5JMP_PMPMP6P7P7P8A6M?^A6M]@FPP_A6M=>P5P>PaPDCD,HM5JMC;C;C;C;C;C;1TM8P3P2g00g3RMg00gSR8'i1h32=OM8dAg514CfbDbGbHX25X35X45X55X65X7519`K/02104\19`\/0V109\f7R9/0`199W,4`'1f9,9Wf:RV'019VK/0W'e10\9149W'1[[[[[[^25^35^45^55^65^75P3PIP;P:PHfJRHPFPWPXPYPZfIRZp,4HdisO<bCbEbF'b%8[14[N'1p,1LRY1_55p,1Xp,3LBX3^RXp,2spRWp,3scrRFP[DA1@Y[#='1'1P0fHR[#814[N'1PYPXPWPFP[DA1@Y[#='1PU15EZO1=3BAP3%8H14HN'1PYPXPWPFfKRHDA1@YH#='1P0PYPXPWPFfLR0DA1@Y0#=PUfM,5EO1=3BAP3PYPXPWPFfNRADAfO,@Y#=PYPXPWPFp,1WPCPUfPp,2HPP`P4P3PAM=\W;W9P4P3O2n2001000000120000000W0WBP4P3O2n2001000000120000000b8XAPX@OP4P3O2n2001000000121000000X0QX?LP4P3O2n2001000000121000000X0RX>JP4P3O2n2001000000121000000X0SX=<P4P3O2n2001000000121000000X0TX<GP4P3O2n2001000000121000000b8W:W1XI5PCPUP:P;C`eo"). Qed.

(* [comment removed for export] *)
Theorem src_owner_upd : PQM.mparser_at segs A T3 T4 vp M' op ois (PQM.with_src s src').
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Upd"] "p'0h04__x1h14__x2h22Hah34__p1h41ch51ni001nh67__arithh74__ffh87__sat10h96__sat7h:6__sat8h;6__sat9h<8__varmaph=5__with>1ah?1Hh@1bhA1pi011phB2EbhC3HTBhD4__x3hE1vi021vhF2HAhG2HChH2HEhI2HNhJ3HOWhK2HPhL1XhM1mi031mhN2n0hO1rhP1EhQ2H1hR2H2hS2H3hT2H4hU2H5hV2H6hW2HBhX3Hs0hY3Hs1hZ2_Hh[3_H0h\3_H1h]2b1h^2b2h_2c0h`2p0ha4p_bbi044p_bbhb4p_bgi054p_bghc7p_depthi067p_depthhd6p_donei076p_donehe6p_morei086p_morehf4p_sbi094p_sbhg4p_ski0:4p_skhh5p_srci0;5p_srchi5p_stki0<5p_stkhj4p_tbi0=4p_tbhk4p_tgi0>4p_tgi0?3cntp%0p&0p;2p;1p;9p;3p;4p;7p;;p;6p;5p;:p;Ip;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0g0013R3p4p710p8P0P3p4p7210p8P0g001OR4p4p710R5p8P0g0020R6p4p710p8P0P6p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R0p4p710R7p1004Ep4p710R8p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R9P2p8P9P8p8P9P7p8P9P5p8P9g007_R5p4p710p8P9p1008<p4p710p8p1008Yp4p7210P8p8g00A9j21Tg00AUj20Tg00B2j16Tg00BWj1;Tg00C<j1ATg00CZj2WTg00D7R8j23Tg01OQj2=Tg01PSl9FTg00DRj2{Tg00nJk10LTg00lJj1MTP5j3LTg0096j1ZTP1j32Tg00T]k20HTg00hQj4ITg00ZUk10CTg00:Tj2kTP6k20<k30?TP3k40:Tg01Fok208Tg00=_j39Tg00;kj1eTP4j3hTg01QWk703Tg01RTl;VTg00PHj2OTg01@2j1vTg01STj3mTg01=Yj1bTg01>Wj1aTg01TOj2zTg01A0j1`Tg01Amj1yTg01Bkj1xTg00>9j1wTg00Y>j3_Tg01UQj6^TP0j5PTg00YXj3]Tg01Cij2uTg01Uoj3[Tg01?Uj2tTg00GOj2sTg00G3j2BTg00H7j3rTg00H[j1YTg00I:j2UTg00Icj3qTg00JLk20KTg00=?k30JTg00KVj2pTg00K8k10ITg00L4k10GTg00LRk10FTg00M=j2XTg00M`j2JTg00NCk10ETg00Ofk20BTg00Pbk20ATg00QNk30>Tg00Qmk40=Tg00Nej1jTg00OCk30;Tg01NMj4TTg00^Ik607Tg011hk105Tg01Vmj3GTg01<Yj4@Tg01K`j1gTg01LCk104Tg01X1k706Tg01Y6j2KTg01Z?j1iTg01[=j2dTg01\@k202Tg01;Wm:01Tg01]DmI00Tg00jPk30@Tg00kjj4~Tg00[Tk40DTg00\2j4oTg00\]j7cTg00]ej8}Tg00Z2j3lTg00]Aj7nTg00^mj6|Tf0R0#6#6#6#Ap=C%60#6p=Ng00_QR4/10p=7g00<DR3@0?30p=:B0@330p=<P3P3f1R6P0C~p=HP3f2R1P6P0H0Dp=EP1g00_oR5g00`NR9P9g00`nR7P3P6g00aNP0Cog00b5R2Fcp=5f3R:P5P9P9P7P1P6P0G}p=81X30p=\1X309l36p=>%60#Ap>09f4R;/1:1060,B1'3p=4Al360p=DP;P5P9P9P7P:P1P5P9P9P7P3P6g00bUP0CoP2FcFnp=?P1P5P9P9P7P6P0Fnp=RP6P5P9P9P7P0E|p=f1116/30p=S1B60,31p=Qp,4Hlayp,2loR2p,2opR<'1S00g00c<S01,0<S02p,2hiR='1S03p,3oisR>,12S04g00d;R?#6R@#6RA#6RB#;S05#6#CRC,0>/1=S06%A@RD%6BS07#NS08#ARE'WRF,1=RG%72RH'3RI'3RJ'3S09'3S0:'3P8Q00Q0:p,4segsRKp,1ARLp,2T3RMp,2T4RNp,2vpROp,2M'RPP<P>p,1sRQp,4src'RR'=RSM9FRTP0Q00Q0:P8Q03Q09PTP0Q03Q09P8Q04PJPTP0Q04P8Q06PIPTP0Q06P8PGPHPTP0PQg01^URTPT1{33RUp,3srcRV$0LRW%M03L%ZURXA2U06%:6RY%<6RZP220H=2R[CI10YZR\p,1LS0;$0CR]'1%AA,0]RA/1Y'k%7Y%7Z11\F'3'3'3'3[^@UR\PUP320<33P6H0:-083R^A2U6;f5R_92U6%::R`%:1Ra593#e%:;%<;P`%<:CI[[[^^U^]UR`%:0%<0P2P[CIRbf6Rc#M92U0Pa%<1PYPZCIRZ[^@U'3XOUp,2WxRY5hUQ0;p,3LBXS0<9LU;p,2spS0=p,3scrS0>p,1WS0?p,1MRaPPK03RdPKPLPMPNPOPaP<P>1=cVM9Ff7Re/=R1=eV/=R59T]J]K]G]H]I]FbLP0g01_Ug01`TRfg01aRRgg01bM#Zf:Rhf9Rif8RjPePcP_P;P:P1P6P0M;V#M9LUWPXf@RXf?RWf>Rkf=Rlf<Rmf;RnPhPiPjPePcM;VRo#M92U0PZ[^@U,3bXOU=hUYPKPLPMPNPOPaP<P>1=oVM9FfAPXPWPkPlPmPnPhPiPjPeM;V/=V/=R,OTWJXKdWGXH`XI^XF\bLWiXg3Xf3Xb3WaXk3WjWhXc3Xd3Xe3PhPiPjPePcP_P;P:P1P6P0O;n011030101;110810710610;10=10>10410510910:10<p,2HARep,2HNp,2HEp,2HCp,2HPS0@p,3HOWS0AO6bM1=QVRV/=RRj99TSPTPjPKPLPMPNPOPPP<P>P0M9FXMT%vQRTAm160S0B59gRh1H:6R\PU%bQR^%aQR`'zRd%`TRm%yQRl#xRk5LURXP\A2U\dA2U\XPUPmPkP\A2U\mA2U\kPgAm:161H;1%`052UXEgA9U\\%wURo92U\1OU\3_PTP0E^3_DP3]DP%MQRQ92U\e'uWBX43X53X@3p,1XRT92U\\h^43^53^@3A[160RY99flRb1H6:RZPUPdPXPZA2UZdA2UZXPUPmPkPZA2UZmA2UZkPfA[:16S0C1H1;%x052UXEfA9UZZA2UZo1OUZ3_PlP0E^3]DP3]DPA2UZQe'uWBXA3X53X43A2UZTRQ\b^A3^53^43Peg01DlS0D1WD`Re'tS0E,H^Rog01J7O2%:oRk%<oRoP2P[CIR[10koRm/1]11Ak'kRA%7kRk%7oRo11mFRm'3R]'3RX'3Rd'3P8P[PdPKPLPMPNPOPPP<P>PjM9FRjP0P8PAPXPjP0P8PkP]PjP0P8PoPmPjP0PKPLPOPaPPP<P>PVPR1sD`R81B4DRN%7`1B4e[[RM%7DRpg00d`RqArD`6UW2R`%7e\q^2pRe1sDERr%7E1B4F[\NRNArDE6VqX2pRE%7F\q^2pRpg00e<Rsg00ehRt#YRu#Y#Y,U31U3u1U3t5q35q3g00fG+0K%wsRt40JS0F%ZsRs1p3:&0I3Ru7E:?E:uS0G1p31Rv7E6&0G3Rw&0F3Rx1X34Ry%;?Rz,J3R{55x&0E9R|Px1J3BS0H95x{P|Px1J3?R}95x{P|A5xy}C8C8C820Bx7RyP0P1g00g3R{g00gSR~'O20A01=9{~dB0>346H0=R4b7b<b=X03X13XD3%76111:11:1%7:[[[^03^13^D3P0P>P2P<fIfRfZO6b6b9b:b;b8%7<eP8PMP`PePrPNPEPpQ0FPsQ0GAEu:v7E6PwPx%;zS0G,J3R2%\DQ08#jS0860;3R~55xP|PxQ0H/>C=5x2P|Px%NzS0H#;#6#CRz,>}R{=5x2P|A5x{~C8C8C8PyP4b7b<b=X03X13XD3116F10:C/11101z/1:10:z/1F[[[^03^13^D3P0P>P=P<fJfNfVO6b6b9b:b;b8Q02/1FR=eP=eg01cOPaPPP<Q01CTeQ0H$09R=P<P0P0P<P=D4P8PMP`PePrPNPEPpp-0RCPtPsAEv6uRvPwPxPx1J3@Ru95x}R~PxPu%\=R2,D}S0HD?P|PxP~PxPuP{D?S01Q05#;#CR{,>}=5xuPxP5P9P9P7P;J07S055Rx,fx5RxS02C8PyP4b7b<b=X03X13W3100=S0F,B69S06P6P1P1P6PzD4S0I106{?S1:g00>YS0J['3S0K[^03^13^3CP0%;@S0L#NS0M#6#CR@,0<S0N,BcPcP<P_O4S0Ob6b9b:b;b8&056R7eW2X>35G<PaPPP<P=C@eg010G,0<S0P%ABR9'0R5Q0G#6#;#CR~P5P0P0P5P~D4P8PMP`PePrPNPEPpPtPsPvPwPxPxQ0H%\9S0G'DS0H=5xuPxPuQ0H/>~D?P|Q02C8PyP4b7b<b=X03X13X3CQ0F/09S0FP6P6Q0FP~D4Q0K[^03^13^3CQ0Ob6b9b:b;b8P7eW2X>33GPaPPP5P~C@ep,4HSRCPKQ08#g%jB#g$04[RBPqV3V3S08US0OPPQ0PP>Q07#A,0>PRK06RRePReg01dT,0<RRPRP0P0PRP9D4P8PMP`PePrPNPEPpPtPsPvPwPxPx1>}@Rq=5xuPxPuQ0G,DqD?P|Q01PxQ05PxPuPqD?,fx5RxRqC8PyP4b7b<b=X03X13X3C100@R~P6P6P~P9D4Q0I106@9Q:1Q0J['3R@[^03^13^3CP010<{R{/1cPcP<P_O4Rcb6b9b:b;b8P7eW2X>37G9PaPPPRP9C@eg01eV,0<R9/KlRR#:R~%<RRRP~P0P0P~PRD4PlPfPfA9f:YPQ[^A3^53^43Q0M#;#CRl,0<RR/K6R~#:R5P;P;P5%<~D4P<P_P_P<PzD4Q0N,B_9S{_#e'3]2]CP0%i:=9fYPQ[^A3^53^43%i6,KRRz#:R~P_P_P~%<zD4P8PMP`PePrPNPEPpPtPsPvPwPxPx1>}lRz=5xuR~PxPu%A?R?,>zD?P|PqC8PyP4b7b<b=X03X13X3C100lRl/16R510l?7Q6P@[^03^13^3CP011{nPnP<P_O4b6b9b:b;b8W2WCXN3P0O1A[_;:=9fYPQ[^A3^53^43Q0C,KRRR#:RQPiPiPQ%<RD4P8PMP`PePrPNPEPpPtPsPvPwPxPxP~PxPu1Dz2D?P|PqC8PyP4b7b<b=X03X13X3C10l=9Q56P@[^03^13^3CP011{WPWP<P_O4b6b9b:b;b8W2WCX`3XN3X_3P1P6P0O3n011020002111003110?100101fDP6O2bEP7eW2X>33GPaPP%yVRW,K9R9#:%<9C@efEP:P1P6P0O4,dZXBbXA3X53X43A9fWYPaPPP6P:CT[^A3^53^43eg01fV,0<RWPWP0P0PWP=D4P8PMP`PePrPNPEPpPtPsPvPwPxPxQ0L#;RY#N#CRf,>}Rb=5xuPxPu1Db2D?P|PqC8PyP4b7b<b=X03X13X3C100fRfP6P6PfP=D4P@[^03^13^3CPcb6b9b:b;b8P7eW2X>37G=PaPPPWP=C@efFP:P1P6P0O4,d\XBhX43X53X@3%vVQ0B59gPaPPP:P6CT[^43^53^@3eg01gV,0<R:P:P0P0P:P=D4P8PMP`PePrPNPEPpPtPsPvPwPxPx%;Y#;#CRY,>}R}=5xuPxPu1D}2D?P|PqC8PyP4b7b<b=X03X13X3C100YRYP6P6PYP=D4P@[^03^13^3CPcb6b9b:b;b8P7eW2X>37G=PaPPP:P=C@eP_%bVR_#7eP0Q0D%aV,WD'tRD,0_/1FeP^P0P0P^Q0ED4Q0;Q0<9LUTQ0=Q0>Q0?PaPPP6Q0@20260N:01W2X>3PaPPP^Q0EC@ePaPPP_PDC@eQ0APKPLQ0OQ08V3VBPOPaP<P>PVM9FeNI00PjeXYmX\oP6P0O2n2001000000121000000X?]XXkP6P0O2n2001000000121000000X?XX[AP6P0O2n2001000000121000000X?dXZ[P6P0O2n2001000000121000000b>bCbWPSP0E^bPXVHXUGP6P0O2n2001000000121000000X?IWTP6P0O2n2001000000121000000X?JWSP6P0O2n2001000000121000000W?WRP6P0O2n2001000000121000000W?WQP6P0O2n2001000000121000000b>o"). Qed.

End Upd.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BUpd.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variable L : heap_layout.
Variables (LBX OB : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte).
Variables (op ois lo hi : Z) (s : PQM.mpst).
Let ob : Z := op + PQM.OFF_BB.
Let W : list L5.range := PGS.W_srcfG (op + PQM.OFF_SRC) ois ++ [(ob, 24)] ++ Wx.

Hypothesis Hceil : hl_ceil L <= lo.
Hypothesis Hsp : sp <= lo.
Hypothesis Hscr : 0 <= scr.
Hypothesis Herr : hl_errno L + 4 <= lo.
Hypothesis Hlay : lo <= op /\ op + PQM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 64 /\ 0 <= lo.
Hypothesis Hdis : op + PQM.PSIZE <= ois \/ ois + 272 <= op.
Hypothesis HA : forall b, In b OB -> apart (fst b) (snd b) lo (hi - lo) /\ (fst b + snd b <= hl_errno L \/ hl_errno L + 4 <= fst b)
                                    /\ 0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= 2 ^ 64.
Hypothesis HC : Forall (fun r => apart (fst r) (snd r) lo (hi - lo) /\ (forall b, In b OB -> apart (fst r) (snd r) (fst b) (snd b))) Wx.
Hypothesis HP : L5C.hpres L (OB ++ LBX) sp scr W M M'.

Lemma frame_clientB a : lo <= a < hi -> 0 <= a < 2 ^ 64 /\ client_addr L (OB ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h02T4h12T3h24__x1h34__x2h44__x3h51Hh67__arithh74__ffh84__p1h94__p2h:6__sat7h;6__sat8h<8__varmaph=5__with>6heq_obh?2Hah@4__x4hA1ahB2H1hC2H2hD2H3hE2H4hF2H5hG2H6hH2a0p;2p;1p;3p;5p;4p;7p;8p;6p-1R0p10000p4p710p9P0p100@bp4p710R1p8P0p10013R2p4p710p8P0P2p4p7210p8P0p1001Op4p710R2p8P0p10020R3p4p710p8P0P3p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R3p1004Ep4p710R0p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R4P1p8P4P0p8P4P3p8P4P2p8P4g007_R2p4p710p8P4p1008<p4p710p8p1008Yp4p7210P0p8g00A9j21Tg00AUj2?Tg00B2j15Tg00BWj1ITg00C<j1CTg00CZj2]Tg00D7R0j20Tg00DRj2WTP2j3UTg00E2j5>Tg00F4j2=Tg00;kj18Tg00G3j2ETg00PHj2OTg00=_j3NTg00GOj2dTg00H7j3bTg00H[j1HTg00I:j2@Tg00Icj3ATg00JLj2KTg00>9j1\Tg00=?j3DTg0096j1[Tg00K8j1ZTg00KVj2JTg00L4j1YTg00LRj1XTg00M=j2FTg00M`j2;Tg00NCj1VTg00Nej1TTg00OCj3STg00Ofj2tTg00Pbj2sTg00QNj3rTg00Qmj4qTg00R_j2pTg00S^j1oTg00T]j2GTg00U:j1mTg00V:j1lTg00W:j2kTg00:Tj2jTg00X@j3eTg00Xcj4LTg00Y>j3cTg00YXj3fTg00Z2j3gTg00ZUj1hTg00[Tj4iTg00\2j4QTg00\]j7RTg00]Aj7aTg00]ej8nTg00^Ij6_Tg00^mj6^Tf2R2f1R4f0R3'E'0p=2%53#5#5#5p=B%53#5p=`g00_QR1/13p=3g00<DR5P2P4P3Cip=7P2g00_oR6g00`NR7P7g00`nR8P5P4g00aNP3CQg00b5R9FRp=4P5P4g00bUP3CQp=:P4P6P7P7P8P3P9FRp=<P2P6P7P7P8P4P3Fap=9f3R9P6P7P7P8P2P4P3Gnp=6P4P6P7P7P8P3E_p=PP4P6P7P7P8P3E^p=Mp,2loR6/13p,2hiR:723p,4Hlayp,2opR;,16R<g00c<,?;/1:R=p,3oisR>,16R?g00d;R@#5RA#5RB#5RC#I#B#C,?>/1:R>%CARD%5C#`RC#CRE']RF,1:RG%36RH'0RI'0RJ'0RK'0RL'0P0P<PL%39?29FRMp,1LRN1W55p,2OBp,3LBX3UROp,2spRPp,3scrRQP9D>1=N9#8'0'0P3P0P=PKf7RR#3?2RFPNPOPPPQPRD>1=NR#8'0'0P3P0P?PJf;RR#3?2RFPNPOPPPQPRD>1=NR#8'0'0P3P0P>PIf?RS#3?2SFPNPOPPPQPSD>1=NS#8'0'0P3P0PGPHfCR0#3?20FPNPOPPPQP0D>1=N0#8'0'0P3fFR0#31E0FRS'0PNPOPPPQP0D>RT1=N0#8RU'0g01fV,?;R;,O5p,2ob=N5;R;eRVP;1dDERW1E1D%3E1E1F[[RX%3DRYg00d`RZAbDE4UW?RE%3F\Z^?YRYp,2T4p,2M'RZO1R[p-0R\\5R]\5R^\5R_P3fJO1R`P^P3fKO1RaP]P3fLO1RbP\p,2T3PZO1RZP^P3fNO1RcP]P3fOO1RdP\g00e<Reg00ehRf#HRg#HRh#HRi,@51@5g1@5fRf5A5Rg5A5g00fGRj'KRk%Hi,@51@5hRh=A5f5A5/KjRf%\eRi5De3D%[eRl%Z5Rm1J59Rn?79m?72m774%Y5Ro%X5Rp1F51Rq%I@,;5Rr54p%V7R7Pp%IB,;5Rs1F5D%TC5S5RD54pRtP7Pp1;5@R@94pr1:@s,<p59pP7A4pq@1:@D,<p59pC6C6C61tp8R8P3P2g00g3Rqg00gSRu'O1s32=NqudAr514CqR1b7b<b=X25X35X45%34119FRu1192f4Rq722RvPM[[[^25^35^45P3P:P6fQRMPRf<RRfPRwO6b6b1b1b1b0b0b0b0b:b;b>PTPU1pO0%oNRO%5C#B#B#B#B#CRC'G/10/0SRS1GPQRQ/10?20P#8RT'0Rx%mN/10%lN7201kN0#8'0R0'jPSPTPVP;PWPXPEPYP[P_P`P^PaP]PbP\PZP^PcP]PdP\ADeki9DefPl1J521J5q?7qm?79m774PoPpPtP7Pp1;5ARt94pr1:ts,<p59pP7Pp1F5C9e5@Rs=4prP7A4pst1:tD,<p59pC6C6C6P8P1b7b<b=X25X35X45X@51G2C/1q1G9C/1q?2qF[\v\u^25^35^45^@5P3P:P6PMPOPRPwp,5HceilO7b6b1b1b1b0b0b0b0b:b;b>PVP;PWPXPEPYP[P_P`P^PaP]PbP\PZP^PcP]PdP\AA5hg/Kj=DeiRiPlA7n2mRn97m4PoPp%IA,;5RA=4prf5,PpRe59pP7PpA4p@AP7f6RA,PpRj1:r@,<p59p,MpC6C6P8P1b7b<b=X25X35X45X8\X9\1124/09Rr1149A2A92g00>YRh[[[^25^35^45^8\^9\P311QM1EM:R:P6PMPPPwp,3HspO7b6b1b1b1b0b0b0b0b:b;b>CL9cx03fPVP;PWPXPEPYP[P_P`P^PaP]PbP\PZP^PcP]PdP\PiPlA7n4mPoPp1;5BRo=4pt=9peP7Pp%CBRB,F59g5@R@=4poP71:t@,<p99pj,MpC6C6P8P1b7b<b=X25X35X45X8\X9\1?4B/191?2B92A9Ph[[\r^25^35^45^8\^9\P3%hNRN/1MP:P6PMPNPwp,4HerrO7b6b1b1b1b0b0b0b0b:b;b>PUeCLCLXGHXFGP4P3O2n2001000000121000000X5IXE>P4P3O2n2001000000121000000X5JXD?P4P3O2n2001000000121000000X5KXC=P4P3O2n2001000000121000000X5LXB<P4P3O2n2001000000121000000bHW?XA5P3O1XA5o"). Qed.
Lemma blk_clientB b a : In b OB -> fst b <= a < fst b + snd b -> 0 <= a < 2 ^ 64 /\ client_addr L (OB ++ LBX) sp scr a /\ ~ in_errno L a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h02T4h12T3h24__x1h34__x2h44__x3h54__x4h61Hh72Hah81bh97__arithh:4__ffh;4__p1h<4__p2h=4__p3h>6__sat5h?6__sat6h@8__varmaphA5__withB4__x5hC4__x6hD4__x7hE1ahF6heq_obhG2H0hH2H1hI2H2hJ3HerhK3HinhL2_HhM2a0p%0p&0p;2p;3p;4p;1p;5p;7p;6p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R0p4p710R5p1004Ep4p710R6p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R7P2p8P7P6p8P7P5p8P7P3p8P7g007_R3p4p710p8P7p1008<p4p710p8p1008Yp4p7210P6p8g00DRk201TP1j3LTg00AUj25Tg00G3j23Tg00T]j2UTg00hQj4VTg00ZUj1bTg00A9j20Tg00B2j16Tg00C<j1FTg00:Tj2ATg00CZj2{TP3j3rTg00E2j5HTg00F4j2GTg00;kj1DTg00D7R3j2ETg00PHj2\Tg00=_j3]Tg00GOj2cTg00H7j3aTg00H[j1?Tg00I:j2WTg00JLj2NTg00>9j1`Tg00=?j3MTg0096j1_Tg00K8j1^Tg00KVj2ITg00L4k100Tg00LRj1~Tg00BWj1KTg00Z2j3RTg00M=j2QTg00Nej1zTg00OCj3yTg00NCj1vTg00M`j2ZTg00Ofj2uTg00Pbj2qTg00QNj3pTg00Qmj4oTg00R_j2nTg00S^j1mTg00U:j1kTg00V:j1jTg00W:j2lTg00Y>j3YTP0j5iTg00Xcj4STg00iRj4hTg00ilj7gTg00^mj6sTP4j3tTg00jPj3fTg00Icj3wTg00[Tj4xTg00\2j4XTg00\]j7[Tg00]Aj7eTg00^Ij6dTg00]ej8|Tg00<DR4f0R07t4p=1Af440p=2f2R1f1R6'0/E0p=9%60#6p=}g00_QR7/06/E0p=41E60,E1p==1070p=;1516/00p=:1W40p=>Aw460p=@P4P1P6P0Cxp=71Z40p=CP1g00_oR5g00`NR2P2g00`nR8P4P6g00aNP0CXg00b5R9F[p=8P4P6g00bUP0CXp=OP6P5P2P2P8P0P9F[p=PP1P5P2P2P8P6P0Fep=<P6P5P2P2P8P0Edp=T%60#6#6#6p=Jf3R9P5P2P2P8P1P6P0G|p=B20144R:p,2OBR;9L:6%11R<%21,5<,36796p,2HAP9P6O2%19R<%29R=p,2loR>p,2hiR?/U>R@CV15<=RAp,1LRB#bRC'0g00d;RD#6RE#6RF#FRG,5CRH/0<'A%FERI%6FRJ#6#}RK#FRL'{RM,0A,4=,4<3=P3f4R<#1R=%2<RAP>P@CV15=ARN/0C10H='A%;=10NM,4A3=13<M,4<PBp,3LBXRA9r:;RNp,2spR=p,3scrROP<DH1GB<#D3=P0f6RP#1%2PP>P@CVf7R@#1RQ%2@RR'5RS/0C10HQ'A%;Q10SM,4R3=P3f8RR#1RS%2RRQ'5RT/0C10HS'A10TM,4Q,4S13RM,4RPBPNP=POPRDH1GBR#D3=P0f:RS#1RQ%2S;:C10HQ'Af;RQ#1RH%2QRTA:HTM'4'4P3f<RT#1RH#;%2TRUA:HUM'413TM,4TPBPNP=POPTDH1GBT#D3=P0f>#1#;f?RU#2RH%1U?:HM'4P3f@R3#2RH#;%13?:HM133M,43PBPNP=POP3DH1GB3#D3=P0fBRH#2#;fCRU#1%2U;:M13UMRV,4UPBPNP=POPUDHRW1GBU#DRX'Ep,2opRYg01fV'5RZ,\4p,2ob=]4ZRZeS00PZ1cILR[137I%;L137M[[R\%;IR]g00d`R^AaIL6UW7RL%;M\^^7]R]p,2T4p,2M'R^O1R_p-0R`\4Ra\4Rb\4RcP0fGO1RdPbP0fHO1RePaP0fIO1RfP`p,2T3P^O1R^PbP0fKO1RgPaP0fLRhO1RiP`g00e<Rjg00ehRk#?Rl#?Rm#?Rn#?Ro#?Rp#?Rq#?Rr#?#>%>p1W4kRk'@'@g00fGRp'N%>r%>q/@k'@/Np%`jRq5Mj3M%_jRr%^4Rs1I4@77@f5Rt,I4?79s77@1I4<Ru?7@s1I4P?7@s771776&004Rv%~4Rw%KERx#K#CRy%KDRz#6R{#6#C5R4R|1Q4I%zK5y4RI58w%v2R}Pw1Q47R~=8wyP}Pw1Z4DRD98wy1OD|,Pw5<wP}Pwf9,Tw1TwS%CzRz%6x#CRx58w%KJ#J#FRJ,Q49R4x%KF#CRF58wA8wFI1TwQ5<w5<w5<w5<w5<wP}Pw%C{1Q4GR{5R4=8wzP}A8w~D1ODI,Pw5<wCBCBCBCBCB1uw8RIP0P1g00g3R~g00gSRz'\1q01=]~zdAp476CoR7b:b@bAX24X34X44X54XB4XC4XD4X;`X<`X=`A:tPM%;P15@R,3199@115@JA9PMT79P99<@9=SQA:PGt13tM,4t[[[[[^24^34^44^54^B4^C4^D4^;`^<`^=`P0%;>g00c<=:Y?10>YfORY#2Rt%1YRYp,3oisP?PCP>fNR>PQP3Php,4Hlayp,4HerrO?b9b1b1b1b0b0b0b0b>b?bFPWPX1nNU%mB%6K#J#J#J#J#F'U?9UV1U=O13U=79U#D'E%kB%jB,3U79U1lBU#D'E'AP:AL:0N%10RBfDR='0%20,5B,3=3=X8:P=AL:=N%1=RN%2=,5N,3U79UP:P;PAP=AL:=;AL:=A;YHDifACSCh3YQ00PZP[P\PLP]P_PcPdPbPePaPfP`P^PbPgPaPiP`%>oRo%>n/@k'@/Np%>m%>l'@,@o/Np=Mjq5MjPrA7s<u?71s1I49?7<s97s<776PvPwPwP5P2P2P8A8w|DAR4D{R{=8wyFgP}Pw%CERE98wy1OE|,Pw5<wP}PwP5P2P2P8A8wDE1OE{,Pw5<wEsCBCBPIP7b:b@bAX24X34X44X54A:190A:0G1'A159<,319991151G,399919g00>Y[[[^24^34^44^54P0PtPYP>PCP=PhO6b9b1b1b1b0b0b0b0b>b?bFPXeCSCSWIWHP6P0O2n2001000000121000000W6WGP6P0O2n2001000000121000000W6WJP6P0O2n2001000000121000000W6WLP6P0O2n2001000000121000000bMW7WKXE4X8:P6P0O2XE4W8o"). Qed.
Lemma cellB_kept a : op <= a < op + PQM.PSIZE -> ~ (op + 280 <= a < op + 320) -> ~ (ob <= a < ob + 24) -> L5C.kept L (OB ++ LBX) sp scr W a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h02T4h12T3h21Hh34__x1h44__x2h54__x3h62Hrh71rh87__arithh94__ffh:6__sat7h;6__sat8h<8__varmaph=5__with>6heq_obh?2H0h@4__x4hA4__x5hB2HahC1bhD4__x6hE4__x7hF1ahG2a0hH1ChI1EhJ2H1hK2H2hL2H3hM2H4hN2H5hO2H6hP3HaphQ2HbhR3Hr'hS2HshT1RhU2_Hp%0p&0p;2p;1p;3p;6p;4p;5p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0g004ER5p4p710R6p8p1004ap6067111111004p1005^p4p771111110p8g006cR7p4p70R8P2p8P8P6p8P8P0p8P8P3p8P8g007_R3p4p710p8P8g011HR8p4p710p8p1008Yp4p7210P6p8g00AUj20Tg00G3j21Tg00B2j1ATg00BWj1JTg00C<j1<Tg00A9j28Tg00CZj2tTg00D7R6j23Tg00DRk20CTP3j3pTg012ij6ITg00PHj2oTg00=_j3cTg00GOk208Tg00H7k307Tg00H[j1ETg00I:j2lTg00>9j1gTg0096j1|Tg00K8j1yTg00L4j1vTg00LRj1uTg00NCj1sTg00M`j2eTg00Ofk20>Tg00Pbk20=Tg00QNk30<Tg00Qmk40;Tg00:TS00j2]Tg01hWk209Tg00E2j5RTg00F4j2PTg00;kj19Tg009Vj2nTg00oIk206Tg00=?j3VTP5j7bTg00:nj2ZTg014mk103Tg0164k502Tg00T]j2iTg00hQj4NTP1j3hTg00X@k300TP8j6~Tg018Cj3}Tg017<j5fTg00Xcj4aTg00Icj3^Tg00JLj2mTg00KVj2{Tg00[Tk404Tg00M=j2zTg00Z2k305Tg00\2j4XTg00\]j7OTg00]Aj7dTg00^mk60:Tg00ilj7xTg00]ej8[Tg00kjj4wTP4k30?Tg00jPk30@Tf2R4f1R8'8f0R1'3p=j%A1#Ap=>1048/81p=6f3R51081,14'3#9p>011848/31#9p=Wg00_QR3/81p=7g00<DR0/l1p=FA^081p=CA^081g00fGR2'mp=Bg00e<R9AV9817V4p=D1{01p=QP0P4P8P1H04p=51e01p=L1z01p=GB05081p=2P0P8g00aNR:P1CXp=HP4g00_oR;g00`NR<P<g00`nR=P0P8P:P1CXg00b5R:FOp=4f5R>P;P<P<P=f4R?P;P<P<P=P5P4P;P<P<P=P0P8g00bUR@P1CXP:FOFdJ0:p=KP4P;P<P<P=P0P8P@P1CXP:FOp=rP5P;P<P<P=P4P;P<P<P=P8P:FOP1Fdp=qP4P;P<P<P=P8P1Fxp=_P0P8P@P1CXp>0BP5P;P<P<P=P4P8P;P<P<P=P1P:FOFdp>0AP5P;P<P<P=P4P8P1G[p=Sf6R@P;P<P<P=P>P?P5P;P<P<P=P4P8P1G[G[p=YP?P;P<P<P=P5P;P<P<P=P4P:FOP8P1G[p=M18?51081,14'3p==1181,34p=UP0P0P8P1Cwp=\Ah781p=@Ac781p=TB0?001p=:B0@001p=;18?51081,14'3#9p=?A^0819^04p=`1m12p=kp,2opR2g00c<,02R:,117j1g00d;R;#ARA#ARB#ARC#JRD#J#A#>#<RE=628P8P2%JAS01#AS02#>RF#A#>#<RGH01p,2obRH%J;RI#>RJ#A#<RK,0HS03,147W4p,4Hlayp,2loRL/82S04p,2hiRM,8:S05p,3oisR:,8LS06%>D#>#<RD=6:MS07%<ARN%AC#>RO#<RP'tRQ,8MS08%7LS09'3S0:'3S0;'3S0<'3S0='3P6Q04Q0=p,1LRR20C00RSp,2OBS0>p,3LBX3pRTp,2spRUp,3scrRVp,1WRWP>EIP1Q04Q0=P6Q05Q0<PRPTPUPVPWf9RXEIP1Q05Q0<P6Q06Q0;PRPTPUPVPWf=S0?EIP1Q06Q0;P6Q07Q0:PRPTPUPVPWfAEIP1Q07Q0:P6Q08Q09PRPTPUPVPWfEEIP1Q08Q09fHRYg01fV,02RZ,o0Ac0HZRZeR[PZ208NPR\113N%7P113Q[[R]%7NR^g00d`R_B07NP8UWBRP%7Q\_^B^R^p,2T4p,2M'R_O1RNp-0R`\0Ra\0Rb\0RcP1fLRdO1PbP1fMReO1PaP1fNRfO1P`p,2T3P_O1R_PbP1fPRgO1PaP1fQRhO1P`g00ehRi#ERj#ERk#ERl#ERm#ERn#FRo%FmS0@1l0iRi'CS0A'BRm%EnRn#ERp#ES0B#FS0C%FkS0D%FjS0E/CiRj'C'BRk%FnS0FQ0D/CiS0G'BRn%FpS0H%FlRl/Cj'B1Cli,Bo%g9Rj5Dk7Dn7Dm3D%|9R9%Q?%y0Rm75>?54m%Q>S0I?5>m?55m758%v0Rn%u0RkPk%JBRp#LRq%GDS0J'2Rr%LIRI'H%s<R<PkPk1e0;R;/HqP<PkPk%LCRs%JJ#>#>#<RJ#GS0K'2Rt/HIP<PkPk1H;sP<PkPkPk%GES0L,2s%LARA54kPkPA%GGS0M,2sEKS0NP<PkPkPk1HsAArkAtCqS0OP<PkA4ktqA4krs5_kP<PkA4k;AS0PPk20BAIH0ACSFYDMDMDMDM20>k=R=P1P4g00g3Rrg00gSRu'o20=14=crudB0<038H0;R3b9b<b=X30X40X50X@0XA0A6?D4188>A6>J?185@f7Ru/0EP>P>PuPGD=g00>YRr[f8RvP@P@PvPJD=f:Rw96XJA6wDX']18uvS0Q?UvX[[[[[[[^30^40^50^@0^A0P1P:P2PMfSS0RPLf@S0SfDS0TPYPdPhfRS0Up,4HdisS0VO<b8b1b1b1b0b0b0b0b:b;b>+09%7Y?UYQPRPTPUPVPYDR1PRY#9'3'3P6fIRx#7?UxQPRPTPUPVPxDR1PRx#9'3PRPTPUPVPWfJEIP1fKRx#7?UxQPRPTPUPVPdDR1PRd#9'3P6PRPTPUPVPeDR1PRe#9PRPTPUPVPWPfEIP1PRPTPUPVfODR1PRg#9%7h?UhQPRPTPUPVPhDRRg1PRh#9Rf1nWhS0W'3Re'3P>PgPeP8PfQ0WP1g010G,02006:Rf1\HKRe%gSRg5VSS0Xp,2WxS0Y5pSPh1@1fRdP11@8fQ00102K%>O#<RO'0Rx%<FRF'\Ry/T410:FS0Z%<CRC'\Rz%Jp#A#>#<S0[,0:S0\%<BS0]'\RB=VSgS0^5VSS0_,@4%:5S0`fURpPpQ0`%;5S0aD?P11Ty5P7Py%:8R{fXR|%;8S0b,0{S0c,1|3W^6dX771@yfP[PZP\P]PPP^P6fZR|#7S0d11|QS0ePxf[R}P}PxPFD?f>S0ff\Rx#7S0gf]S0h/1QS0iPNPcP1f_R~O1S0jPbP1f`S0kO1S0lPaP1faS0mO1S0nP`P_PbP1fcO1S0oPaP1fdS0pO1S0qP`PjP9%Q4?58mS0rPnPkPkPkQ0L,2;=4kAPkPAQ0M,2;EKP<PkPk%GK,2;S0s%GO'2S0t=4kAPkPAQ0t%GFS0u'2EKCSP=P3b9b<b=X30X40101EP8P8P1PGD=Pr[108KS0t/0OROP4P4POPFD=Pr[[^30^40P1ffS0vP2Q0pO3b8b1b1b1b0b0b0b0W?W2P8P1O2n2001000000121000000b:b;b>%:yS0wfWROPOQ0w%;yD?eW6P?P1P5FbW2P1O1Q0_,@5Q001Tz?Q0^,@?%:>RyPOPOPy%;>D?P11Tz>P7PzQ0c,1|9W{|^6dX771@zfP[PZP\P]PPP^P6Q0g11xQQ0ZQ0hQ0hQ0ZPCD?Q0Sf^Ry#7S0Z11~QPNPcQ0nPbP1fbO1PaQ0oP`P_PbP1feS0_O1S0wPaP1Q0vO1P`Q0DQ0E5`lS0D#kS0xQ0G,BoQ0@Q0G'CS0G#kQ0x;Dj3DS0xP9%Q5?55m?54m?58mS0@PnPkQ0NP<PkQ0OP<PkA4kt;Q0J,2;=4ks5_kS0yP<PkPkQ0u,2;Rs=4kAPkPA%GC,2sEKCSFYP=P3b9b<b=X30X40X50104EP8P8P4PGD=Pr[S0uP5P4P4P5PJD=RsA6?J4A64D?']Rt105FRFP?P?PFPCD=Pr[[[[^30^40^50P1P2fhRCP:Q0vfgS0zQ0VO6b8b1b1b1b0b0b0b0W?W2P8P1O2n2001000000121000000b:b;b>%:zS0{fYRFPFQ0{%;zD?eW6P@P1P>FbW2P1O1Q0^,@>Q001TB@1@@g%:uRzPFPFPz%;uD?P11TBuP7PBQ0c,1x9W{x^6dX771@BfP[PZP\P]PPP^P6Q0Z11yQQ0\P~P~Q0\Q0]D?fBQ0k#7Q0m/1QPNPcQ0oPbQ0qPaQ0wP`P_PbP1Q0zO1PaP1PCO1P`Q0xP9Q0@PnPkQ0NP<PkQ0OP<PkQ0yP<PkPkQ0[#G,2;Rd=4kAPkPAQ0]#G,2dEKCSFYP=P3b9b<b=X30X40X50Q0uQ0[,05RdP?P?PdQ0]D=Pr[\t\s[^30^40^50P1P2fjP:PCfiQ0VO6b8b1b1b1b0b0b0b0W?W2P8P1O2n2001000000121000000b:b;b>%:BRCP}P}PC%;BD?eW6PvP1PuFbW2P1O11@ugPr%:XRBP}P}PB%;XD?RBP1n010000000W2P1O1n200100000021100010000W2P1O1n200100000021100011000W2P1O1n200100000021100011000fTRC,Z4#9RsebRW6X771nfheQ0XQ0YPhPePgPhP[PZP\P]PPP^P6%7C11CQQ03,1p9WHpPvfV#711OQPNPcP1PFO1PbP1P|O1PaP1P}O1P`P_PbP1Q0hO1PaP1PyO1P`PjP9Q0rPnPkPkPkQ0PPkPAQ0sEKRyP<PyCSP=P3b9b<b=X30X40P1P8P8P1PKD=Pr[Q0t,149j84Pr[[^30^40P1Q0kPHQ0hO3b8b1b1b1b0b0b0b0W?W2P8P1O2n2001000000121000000b:b;b>%:eRHPhPhPH%;eD?e1Zeh#9e&03hI02Q0YP7%:1%;1PL1iMLReCNQ0>9hS1RH%:4%;4P{Q0bCN[^CS'3X7SRKQ0U,Z1#9X77PKP1O1P6P{Q0bPLPeCNQ0`Q0aP{Q0bCN\H^CSPsP1Q0`Q0aPLPeCN%:@%;@P{Q0bCN\H^CSP[PZP\P]PPP^P6Q0dQ0ePBQ0fQ0gQ0iPNPcQ0jPbQ0lPaQ0nP`P_PbQ0oPaQ0qP`Q0B#ER`#E#FRa%F`Q0D'C'BR`Q0HQ0E7`l,BaRlQ0FQ0A'C,BaQ0CQ0G'C,BaQ0F?`oi,BaRa?Daj3D9Dl`3DP9%Q@?5um95m4Q0I?5?m%Qu?5um755758PnPk12;IRIQ01#LRn54kQ02#LRm>000n,2n=4k;5_kP<PkQ01#J#LR;Q0J'2R?=4kmP<PkPk1Hn;P<PkPkQ0K,2qR9/HmP<PkPk1HnqP<PkPkPkQ0L,2q=4kAPkPAQ0M,2qEKP<PkPkPk1HqAArkA9CqP<PkA4k9;A4k?q5_kP<PkPkQ0PPkPAPIEKCSFYDMDMDMFYP=P3b9b<b=X30X40X50X@0XA0XD0XE0A61451i>5=651']A6uD@18>vA6uJvQ0Q10XEP@P@PXPGD=Pr[PwPuPuPwPJD=f;RuQ0?76JQ0??6Du']PvPXPXPvPwD=Pr[[[[[[[[[^30^40^50^@0^A0^D0^E0P1P:PMP2PLQ0T#;Q0vQ0T#:Q0SQ0RPOP}P~Q0pQ0_Q0VO?b8b1b1b1b0b0b0b0W?W2P8P1O2n2001000000121000000b:b;b>1Z>O#9eWUWPP8P1O2n2001000000121000000W2X77Q0Yp,2HCE~7}hDfDfQ0WeCaCaCaWIWHP8P1O2n2001000000121000000W2WTP8P1O2n2001000000121000000bGPRPTPUPVPWPYEIeWOWNP8P1O2n2001000000121000000W2WMP8P1O2n2001000000121000000W2WLP8P1O2n2001000000121000000W2WKP8P1O2n2001000000121000000W2WJP8P1O2n2001000000121000000bGWQWSWBXF0P1O1XF0o"). Qed.
Lemma cellB_ag a0 n : op <= a0 -> a0 + n <= op + PQM.PSIZE -> (a0 + n <= op + 280 \/ op + 320 <= a0) -> (a0 + n <= ob \/ ob + 24 <= a0) ->
  L5C.agree_on M M' a0 n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h02T4h12T3h24__x1h34__x2h44__x3h54__x4h62Hah77__arithh84__ffh96__sat5h:6__sat6h;8__varmaph<5__with=6heq_obh>4__x5h?2a0h@1nhA2H1hB2H2hC2H3hD2H4hE1ap;2p;1p;3p;4p;:p;7p;8p;6p-1R0p10000p4p710p9P0p100@bp4p710R1p8P0p10013R2p4p710p8P0P2p4p7210p8P0p1001Op4p710R2p8P0p10020R3p4p710p8P0P3p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R3p1004Ep4p710R0p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R4P1p8P4P0p8P4P3p8P4P2p8P4g007_R2p4p710p8P4p1008<p4p710p8p1008Yp4p7210P0p8g00A9j21Tg00AUj22Tg00B2j16Tg00BWj1<Tg00C<j1ATg00:Tj2CTg00G3j25Tg00D7j2:Tg00DRj2RTP2j3QTg00PHj2ITg00=_j3NTg00GOj2fTg00CZj2cTg00H7j3]Tg00H[j1FTg00I:j2BTg00JLj2ETg00>9j1YTg00=?j3DTg0096j1XTg00K8j1WTg00KVj2GTg00L4j1VTg00LRj1UTg00M`j2=Tg00NCj1PTg00Ofj2OTg00Pbj2STg00QNj3TTg00Qmj4gTg00M=j2HTg01i`j4eTg01;Wl:dTg01<Yj4bTg00Icj3_Tg00[Tj4^Tg00\2j4LTg00\]j7JTg00Z2j3\Tg00]Aj7[Tg00]ej8`Tg00ilj7aTg00^mj6ZTf2R2f1R0'2f0R4'1p=4%64#6p=;g00<DR3?_04p=7P3P2P0P4C^p=0P2g00_oR1g00`NR5P5g00`nR6P3P0g00aNP4CLg00b5R7FJp=3A\304p=9P3P0g00bUP4CLp=@P0P1P5P5P6P4P7FJp=>P2P1P5P5P6P0P4F[p=?f3R7P1P5P5P6P2P0P4G`p=8P2P1P5P5P6P0P4Fap=MP0P1P5P5P6P4EZp=Kp,2opR1/10g00c<R8,219420g00d;R9#6R:#;R;#<#<#6#;#AR<,219472%<:R=#;#;#;#AR>=417'Cf4R?p,2obR@747%<9RA#6RB#6RC#6#ARD=4@?'Cf6RE/14f5RF,2E,54':p,1L1R33p,2OBp,3LBX3Qp,2spp,3scrp,1Wp,1MRGp,2M'RHP0p,2HPP0g01fV,21RI,I3AN3@IRIeRJPI%A:RK%6;#;#AR;'fRLg00_QRM/5K11M;1cK;RN,5M[[RO11MKRPg00d`RQA]K;0UW6R;11MN\Q^6PRPp,2T4PHO1RQp-0RN\3RK\3RR\3RSP4PFO1RTPRP4PEO1REPKP4f7O1RUPNp,2T3PHO1RVPRP4f9O1RWPKP4f:O1RXPNg00e<RYg00ehRZ#FR[#FR\#FR],B3R^1B3\R\1B3ZRZ'7R_'7g00fGR`'E%F],B3R]1B3[R[/7Z'7/E`%YYRZ5DY3D%XYRa%W3Rb1G3F70F?02b1G3?Rc?0Fb90b7700%V3Rd%U3Re%<=,=3R=1=3:R:53e1=3CRC,9=Rf,@:,>e5?eRg%P5R5Pe1=39R91=3A'9RA93efP5PeA3e9=P5A3e9:Rh1@:A,>e5?eC8C8C81Oe6R6P4P2g00g3RAg00gSRi'I1S42=NAidAT3M0CgRMb8b;b<X23X33X43X53X>31170127?Ri,50':120794?F112F117?127F,5?':[[[^23^33^43^53^>3P4fARAfBRjP8f<R8P1f;Rkf?f@O8b7b1b1b1b0b0b0b0b9b:b=PJPIPLPOP;PPPQPSPTPRPEPKPUPNPVPRPWPKPXPN17\[,7^/E`17]_/E`=DYZ5DYRYPaA0b?cRc?02b1G37RZ?0?b90b?700PdPePgP5Pe1H3<,99Rg93ef1H3>,99Rf=3e=5MeP5A3eg:1@:f,>e5?e,KeC8C8P6PMb8b;b<X23X33X43X5311201227,50':Rf120<,1iA40>7'CA42<7122>,57':g00>YR>[[[^23^33^43^53P4PAPjP8P1Pkf>O6b7b1b1b1b0b0b0b0b9b:b=PJPIPLPOP;PPPQPSPTPRPEPKPUPNPVPRPWPKPXPNPYPaA0b?Z?02bA0c?b700PdPeA3eC:%<B,=3,9CRB,@:,>e5?eP5PeA3eB91H3D,99R9=3eC5MeP51@:9,>e9?eh,KeC8C8P6PMb8b;b<X23X33X43X5311i0A40D7'C1127122D,57':P>[[\f^23^33^43^53P4PAPjP8P@Pkf=O6b7b1b1b1b0b0b0b0b9b:b=CeM:dW6XE3PGPHPFP?CbeWDWCWBWAX@3X?3P0P4O2X@3X?3o"). Qed.
Lemma blkB_kept b a : In b OB -> fst b <= a < fst b + snd b -> L5C.kept L (OB ++ LBX) sp scr W a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h02T4h11Hh22T3h34__x1h44__x2h54__x3h64__x4h74__x5h84__x6h94__x7h:2Hrh;1rh<2H0h=7__arithh>4__ffh?6__sat7h@6__sat8hA8__varmaphB5__withC1bhD6heq_obhE2HahF2a0hG2_HhH1ahI1ChJ1EhK2H'hL2H1hM2H2hN2H3hO2H4hP2H5hQ2H6hR4HapbhS4HapfhT3HinhU3Hr'hV1Rp%0p&0p;2p;3p;4p;1p;5p;6p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0g004ER5p4p710R6p8p1004ap6067111111004p1005^p4p771111110p8g006cR7p4p70R8P2p8P8P6p8P8P0p8P8P3p8P8g007_R3p4p710p8P8g011HR8p4p710p8p1008Yp4p7210P6p8g00DRk20?TP1j3eTg01jfk404Tg00B2j1;Tg00C<j1?Tg00CZj2pTg00G3j22TP3j3oTg00E2j5UTg00F4j2RTg00;kj1<Tg00D7R3j27Tg012ij6kTg009Vj2ETg00T]j2cTg00hQj4ATg00AUj23Tg00ZUj1|Tg00A9j24Tg00:TS00j2MTg00BWj1JTg00oIj2qTg00>9j1gTg00=?j3WTg00PHj2fTg00=_j3^Tg00GOk20>Tg00H7k30=Tg00H[j1CTg00I:j2mTg0096k10<Tg00KVj2\Tg00K8k108Tg00L4k107Tg00LRk106Tg00NCk103Tg00M`j2jTg00X@j3iTg00Ofk201Tg00Pbk200Tg00QNj3~Tg00Qmj4}TP5j7bTg00:nj2XTg014mj1{Tg0164j5zTP8j6wTg018Cj3yTg017<j5hTg00Xcj4aTP4j3vTg00jPj3uTg00kjk402Tg00Icj3dTg00JLj2tTg00[Tj4sTg00M=k205Tg00Z2j3rTg00\2j4lTg00\]j7nTg00ilk709Tg00]Ak70:Tg00^mk60;Tg00]ej8`Tg00<DR4f0R87v4p=1Au448p=0f2R5f1R1/38'2p=Q1451/78p=H%;8#;p=Bg00_QR6/41/78p=K1718,75p=[1468p=81351/48p=:P4P4P1P8H02p=]Ae718p=@A^718p=Sf4R0f3R2'41318,25'7#<p=91451/78#<p=_1m48p=GAd418p=PAd4189d45p=Tg00e<R9g00fG,t1;W8p=IP4P5P1P8Csp==1j48p=D20548p=FAr418p=6P5g00_oR:g00`NR;P;g00`nR<P4P1g00aNP8Clg00b5R=Fnp=5P5P:P;P;P<P1P8K09p=ZP4P1g00bUP8Clp=OP1P:P;P;P<P8P=Fnp=LP5P:P;P;P<P1P8K0:p=NP1P:P;P;P<P8J0;p=VP2P:P;P;P<P5P1P8G`p=Yf6R=P:P;P;P<f5R>P0P2P:P;P;P<P5P1P8G`G`p=>1218,75p=x20?44R:p,2OBS019e:1%15S02Q02%05S035Q17H1P2P5P1P8H04g00d;R?#;R@#?RA%;@RB#;RC#;#BRD#?RE'pRF,25,K5p,1LRGQ01p,3LBX5o:RHp,2spRIp,3scrRJP5DU1RG5#<3[P3122F,K2PGPHPIPJP2DU1RG2#<'7PGPHPIPJp,1WRKP0EkP812>F,K>PGPHPIPJP=DU1RG=#<'7P3PGPHPIPJf7RLDU1RGL#<PGPHPIPJPKf8RMEkP8PGPHPIPJf9RNDUf:RO,RG#<f;RP12PF'KPGPHPIPJPPDURJ1RGP#<RI1EKPRH'7RQ'7P>PJPQP1PIPHP8p,2HAf<RHPOO2%1HRI%0HRHp,2loRQp,2hiRJ/cQRRCA13IHRS%|GRG'4%?BRT,3GRU/4I'M14SF,KH,KI3[P3f=RI#1RH%0IRSPQPRCA13HSRV/4G14UH'M%8H14VF,KS3[1EKIP8f?S04#1Q04#0PQPRCAf@RI#1RS%0IRI'3RV/4G14US'M%8S14VF,KI3[p,4Hlayp,2opRI,4QS05g00c<=:IJS06p,3oisRV,4QS07%JC#B#B#?RS=:VJS0814JFS09%8QS0:'7S0;'7S0<'7S0='7S0>'7P3Q05Q0>fB,EKP8Q05Q0>P3Q06Q0=fF,EKP8Q06Q0=P3Q07Q0<fJRU,EKP8Q07Q0<P3Q08Q0;fNS0?,EKP8Q08Q0;P3Q09Q0:fRS0@,EKP8Q09Q0:g010G,3I/qVRGp,2obS0A%J?S0B#;S0C#;S0D#;#?RH']RW%g:RX5W:S0Ep,2WxS0F5o:fURY1@8GRZP81@1GQ0013IH%BD#?RD'3R[%J@R\#;R]#B#?R^']R_/S513V^S0G%?CR`']Ra%JBRb#J#;#B#?Rc,3VS0H/]TRd=W:XRe5W:Rf,@5%12S0IfYS0JQ0JQ0I%02S0KD9P81S_2P7P_%11Rgf\Rh%01S0L,3gRi,2h3_^:ZX;71@_Gg01fV,3IRj,f4Q0A=^4jRjeS0MPj20>AES0N126A%8E126F[[S0O%8ARkg00d`RlB0=AE1UWES0P%8F\l^EkS0QP3f^Rk#812kFP[f_RlPlP[P^D9fXR[f`RE#8S0RfaRA/2Fp,2T4p,2M'RmO1Rnp-0Ro\4Rp\4Rq\4RrP8fcRsO1PqP8fdS0SO1S0TPpP8feRtO1S0UPop,2T3PmO1RmPqP8fgO1S0VPpP8fhS0WO1S0XPog00ehRu#CRv#CRw#CRx#CRy#CRz#GR{%GyRy%GwS0Y%GvS0Z'PS0['PS0\'P%CzS0]#GS0^%GxRx1m4uRu5TyS0_'P%g9Rz'I'IS0`&0<9R91\40S0a&084Rv7=21\4=?=Lv7=51\4>S0b?=Lv1\4L?=Lv7=L7=1S0c&074Rw&064R|%DbRb%FSS0d'6%DCRC55|S0e&03;R;P|1j4?R?Q0D#J#B#B#?R}#FS0f'6=5|CS0gP;P|%DBRB=5|?S0hP;P|%D]R]%J\S0i#D'6R\=5|BS0jAi4CB,6B=5|]5Z|S0kP;P|%D@R@95|]1O@\,L|5N|S0lP;%FHS0m,6?%FD'6R\=5|@%F^S0n,6\,O@,L|5N|,V|CYF>F>201|<R<P8P5g00g3R\g00gSR~'f20085=^\~dA~461C}R6b>bAbBX34X44X54X64X74X84X94A:0S2S0oA:1}0S0p1405R~A:MN>1c=>=:>M'MS0q13NOS0r,2>9HN>S0s13>H/3DRDAQ=D^7H=g00>YRD[[[[[[^34^44^54^64^74^84^94P8fkR\#0%1\PVPJPQfjS0tPIPUQ0@fVS0uf[RUQ0WO<b=b2b2b2b0b0b0b0W<W1P1P8O2n2001000000121000000b?b@bD%1_S0WPUPUQ0W%0_D9eW:P0P8P2FbW1P8O11@2fQ001Sa01@0e%1>S0WPUPUQ0W%0>S0vD9P81Sa>P7Pa12ki9_gk^:ZX;71@aGQ0MPjQ0NQ0OQ0PQ0QP3Q0R12EFQ0GPAPAQ0GP`D9fZRffbR_#8S0G12sFPnPrQ0UPqP8ffO1S0RPpQ0VPoPmPqP8fiS0wO1S0xPpP8Q0tO1PoQ0]#CS0]#CS0y#C#G1Pyu7T{Q0]#GQ0Y=Tyu7T{Q0y#GQ0Z,Px7T{Q0^Q0[,Px7T{/Iz'I'I'IS0^P9Q0cPwP|Q0d,6?R{=5|bS0dP;P|Q0hP;P|Q0f,6CRx=5|bS0fP;P|A5|BCS0[P;P|Q0jAi4bB,6B=5|]5Z|R]P;P|Q0lP;P|A5|x?A5|{C5Z|R{P;Q0n,6?RC=5|@%F`,6C,O@,L|5N|,V|CYF>F>F>P<P6b>bAbBX34X44X54X64X74X84X94A:8S0RC1421RxA:>}=RB14>=RbQ0r/4=1cM==:=N'MRuAQ=OP9HO=RPA:N}=A:=SN'MRS13L^R^AQM^`7HMPD[[[[[[[[^34^44^54^64^74^84^94P8fmR^#0%1^PJPIPQflR^PVfLS0rfPS0nfTP[f]R`Q0tp,4HdisR}O>b=b2b2b2b0b0b0b0W<W1P1P8O2n2001000000121000000b?b@bD%1aRyP`P`Py%0aD9eW:P=P8P>FbW1P8O11@>eQ001Sd=1@=X%1LReP`P`Pe%0LD9P81SdLP7Pd12Ei9_gE^:ZX;71@dGQ0MPjQ0NQ0OQ0PQ0QP3Q0G12_FRZQ0HPsPsQ0HPTD9PhQ0S#812tFPnPrQ0VPqQ0XPpQ0xPoPmPqP8P\O1PpP8P^O1PoQ0^P9Q0cPwP|Q0dP;P|Q0hP;P|Q0fP;P|Q0[P;P|P]P;P|Q0lP;P|P{P;%Fc,6?R{=5|@%FT,6{,O@,L|5N|,V|CYF>F>F>P<P6b>bAbBX34X44X54X64X74X84X9413LcRcAQMcT7HMPD[\S\P\u\b\B\x\C^34^44^54^64^74^84^94P8foRC#0%1CPJPIPQfnPVQ0?Q0@Q0uPfPlP^P}O>b=b2b2b2b0b0b0b0W<W1P1P8O2n2001000000121000000b?b@bD%1dR}PlPlP}%0dD9eW:PMP8PLFbW1P8O11@LXPD%1NRLPlPlPL%0ND9P8n010000000W1P8O1n200100000021100010000W1P8O1n200100000021100011000W1P8O1n2001000000211000110001X5[#<RNebUW:X;71EGYeQ0EQ0FPYPWPXPYQ0MPjQ0NQ0OQ0PQ0QP3%8[12[FQ0i#;#B#B#?R[,3IRXQ0JQ0JPXPHD9Q0@%8f12UFPnPrP8P`O1PqP8PkO1PpP8PlO1PoPmPqP8PAO1PpP8P_O1PoQ0`P9Q0cPwP|Q0eP;P|Q0gP;P|Q0hP;P|Q0kP;P|Q0lP;%F[,6?Rk=5|@Q0m,6k,O@,L|5N|,V|CYF>F>P<P6b>bAbBX34X44X54X64X74X84X94Q0oQ0pQ0qQ0s13>[R[AQ=[H7H=PD[[[\~[[^34^44^54^64^74^84^94P8%0t%1tPVPJPQQ0SPIfDQ0rQ0nPYP_O<b=b2b2b2b0b0b0b0W<W1P1P8O2n2001000000121000000b?b@bDQ0APYPYQ0APHD9e%1WRHPYPYPH%0WD9e1XWY#<e%{YDzQ0FP7%18%08PQPRCAQ019e:8RWQ02Q03PgQ0LCA[^C:'7X;:RHQ0u,X8#<X;7PHP8O1P3PgQ0LPQPRCAQ0IQ0KPgQ0LCA\W^C:PNP8Q0IQ0KPQPRCA%1=%0=PgQ0LCA\W^C:P8PhPfO2Q0WQ0v%1h%0hCAQ0MPjQ0NQ0OQ0PQ0QP3%8l12lF%1ORlPEPEPl%0OD9Q0J%8APnPrQ0TPqQ0UPpQ0RPoPmPqQ0XPpQ0xPoQ0\Q0_/Iz'IP9Q0a9=v>?=5vQ0b9=v>?=2v7=1PwP|Q0B#D,6?RwQ0D#DRv55|Q0C#J#D,6vR9=5|?5Z|P;P|A5|v@1O@9,L|5N|P;A5|?@1O@w,L|5N|,V|F>P<P6b>bAbBX34X44X54X64X74A:852A:208'M130>9x~5AQ2509H52PD[[[^34^44^54^64^74P8%0^%1^fER^#0P\%1^Q04Q0wO7b=b2b2b2b0b0b0b0X<ZW1P1P8O2n2001000000121000000b?b@bDbK1X>U#<eWRWGP1P8O2n2001000000121000000W1X;7Q0Fp,2HCEw7yYDhDh1EKYRYePYeWQWPP1P8O2n2001000000121000000W1WOP1P8O2n2001000000121000000W1WNP1P8O2n2001000000121000000W1WMP1P8O2n2001000000121000000W1WLP1P8O2n2001000000121000000bFWGWSP1P8O2n2001000000121000000bFCaCaCaWJWIP1P8O2n2001000000121000000W1WVP1P8O2n2001000000121000000bFWEWTXH4XC:P1P8O2XH4WCo"). Qed.
Lemma blkB_dkr b : In b OB -> PQMF.dkr M M' (fst b) (snd b).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h01bh11Ch21Dh31Eh41Hh52Hah63Hinh71Rh81ah92a0p;2p;3p;1p;4p;5p;=p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0p1004Ep4p710R5p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R6P2p8P6P5p8P6P0p8P6P3p8P6g007_R3p4p710p8P6p1008<p4p710p8p1008Yp4p7210P5p8g00DRj2GTP1j3FTP4j3;Tg00A9j25Tg00jPj3<Tg00AUj2DTg00G3j26Tg00D7R4j20Tg00B2j12Tg00Nej19Tg01K`j1>Tg01LCj1=Tg01Lej27Tg00NCj1ETg00=_j38Tg00;kj11Tg01jfj4CTg00C<j1:Tg00CZj2BTP3j3ATg00E2j53Tg00F4j24Tg01MKl=@Tg01NMj4?Tg00<DR3/G3R1f0R5p,2OBR65F1f2R09;33R2/55A<330,D2,65'0g00d;#2R2#2#2R7#9#>R8#=R9p,1MR:%27#2#2R7#9R;f1R<'7O1%E8R838#1f4R=P0f3R>P<CCg00_QR?/50%:2%:7'BR7,60'0p,1LR2p,3LBX9A16R6p,2spR@p,3scrRAP0D31420#1'0'0P415?>16>7'0P2P6P@PAP>D3142>#1'0p,2M'R>17;=O1=898#1P5f5R=,5?16=7'0P2P6P@PAf6R7D31427#1'0P4P2P6P@PAf7R4D31424#1P>f8,7;O1=898#1P5P2P6P@PAf9R8D3f:,42#1P2P6P@PAp,1WP:P>f;p,2HPP=P<P5P8M=@W3W1P<P5O2n2001000000120000000W4W7P<P5O2n2001000000120000000b9W2W5X83P:P>A;33<A<33<C?eW6X01P5O1W0o"). Qed.
Lemma frameB_dkr : PQMF.dkr M M' op PQM.PSIZE.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "h01Hh12T4h22Hah32T3h44__x1h54__x2h64__x3h74__x4h84__x5h94__x6h:2a0h;1Ch<1Dh=1Eh>2H1h?2H2h@2H3hA2H4hB2H5hC2H6hD1RhE7__arithhF4__ffhG6__sat7hH6__sat8hI8__varmaphJ5__withK1ahL6heq_obp;2p;1p;3p;4p;7p;5p;=p;8p-1R0p10000p4p710p9P0p100@bp4p710R1p8P0p10013R2p4p710p8P0P2p4p7210p8P0p1001Op4p710R2p8P0p10020R3p4p710p8P0P3p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R3p1004Ep4p710R0p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R4P1p8P4P0p8P4P3p8P4P2p8P4g007_R2p4p710p8P4p1008<p4p710p8p1008Yp4p7210P0p8g00A9j21Tg00AUj25Tg00G3j27Tg00D7R0j20Tg00B2j12Tg00Nej1OTg01K`j1ZTg01LCj1XTg01Lej24Tg00NCj1LTg00BWj1BTg00C<j1GTg00CZj2jTg00PHj2NTg00=_j3HTg00GOj2]Tg00H7j3[Tg00H[j1;Tg00I:j2MTg00JLj2FTg00>9j1WTg00=?j3CTg0096j1VTg00KVj2ETg00K8j1UTg00L4j1TTg00LRj1STg00M`j2>Tg00M=j2RTg00Z2j3ITg00\2j4DTg00ilj7QTg00Ofj2iTg00Pbj2hTg00QNj3gTg00Qmj4fTg00:Tj2eTg01hWj2`Tg00DRj2_TP2j3^Tg00E2j5@Tg00F4j2ATg00;kj1<Tg01MKl=\Tg01NMj4aTg00Icj3bTg00[Tj4cTg00\]j7PTg00]Aj7dTg00]ej8YTf2R2f1R4f0R33H#<p=3g00_QR1/13p=8g00<DR5/M3p==Ab543p=9P5P2P4P3Ccp=:P2g00_oR6g00`NR7P7g00`nR8P5P4g00aNP3CDg00b5R9FPp=6P4P6P7P7P8P3P9FPp=JP2P6P7P7P8P4P3Fdp=Kf3R9P6P7P7P8P2P4P3GYp=?p,2opR:/13g00c<R;,5:R<,73'0g00d;R=#2R>#2R?#2R@#O#ZRA#XRBp,1MRC%2@#2#2RD#ORE/44O1%LARA33p,4Hlayp,2loRF/1:RGp,2hiRH,1<R<p,3oisRI,1FRJ%B@#2#2#2#2#GRK,5I/1HRL%G>RM%GDRD'jRN,1HRO%8FRP'0RQ'0RR'0RS'0RT'0P0PGPTp,2M'RUf4RV,4EO1=3BAP3P0P<PSPUf8RW,4EO1=3BAP3P0PJPRPUf<,4EO1=3BAP3P0PLPQPUf@RX,4EO1=3BAP3P0POPPPUfDRY,4EO1=3BAP3fGRZg01fV,5:R[,N5p,2ob=H5[R[eP[1]MD171M%8D171N[[%8MR[g00d`R\A[MD4UW2%8N\\^2[p,2T4PUO1p-0R[\5R\\5RD\5P3fKRMO1PDP3fLR]O1P\P3fMR^O1P[p,2T3PUO1PDP3fORDO1P\P3fPR\O1P[g00e<R[g00ehR_#;R`#;Ra#;Rb#;Rc#=%=bRb1M5_R_'9'9g00fGRd'F%;cRc#=%=a/9_'9/FdRa%;c#=%=`/9_,9b'9/Fd%W[5C[9C[a5C[3C%V[1E5Vf6R[%U5Ra3:1E5[?:[a7:2f5Rd,E5?:[a?:9a7:4%T5%S5Ra%B>#2,>5Rb1R5K5I5R_%B=,>5R`56a%L7RcPa1>5=R==6abPcPa1>5@R@%B?,>55I5R?=6a`PcPaA6a=@PcPa1>5>R>96a@P5P>g00bUReP?CD,Ja5KaPcPaPaP6P7P7P8A6a?bA6a_@FQPcA6a=>P5P>PeP`CD,Ja5KaC?C?C?C?C?C?1ia8P3P2g00g3Rag00gSR8'N1h32=Ha8dAg514CfbFbIbJX45X55X65X75X85X9515dK/12114[15d[/1V119[f7R9/1d159W,7d'0f9,5Wf:RV'115VK/1W'e11[9179W'0[[[[[[^45^55^65^75^85^95P3PIP;P:PHfRPFPXPYfHRYP]fQp,4HdisO<bEb3b3b3b1b1b1b1bGbHbL'`%8Z17ZN'0p,1LRX1_55p,2OBp,3LBX3^RFp,2spRHp,3scrRIPZD@1AXZ#<'0'0P0%8Y17YN'0PXPFPHPIPYD@1AXY#<'0PUfI,4EO1=3BAP3fJRY#817YN'0PXPFPHPIPMD@1AXM#<'0P0PXPFPHPIP]D@1AX]#<PU14E^O1=3BAP3PXPFPHPIfNRAD@1AXD#<PXPFPHPIp,1WPCPUP\p,2HPPdP4P3PAM=\W=W;P4P3O2n2001000000120000000W0WDP4P3O2n2001000000120000000b:XCPXBOP4P3O2n2001000000121000000X0QXALP4P3O2n2001000000121000000X0RX@JP4P3O2n2001000000121000000X0SX?<P4P3O2n2001000000121000000X0TX>GP4P3O2n2001000000121000000b:W<W2XK5PCPUP:P;Caeo"). Qed.

(* [comment removed for export] *)
Theorem vec_owner_upd (src src' : PM.srcst) (x x' : PQV8.v8) (g g' : Z) :
  OB = PQM.vec_rest_own s ->
  PQV8.vw_at (PQM.vec_owner segs A T3 T4 vp op ois lo hi s) M src x g OB ->
  PM.src_fields_at segs T3 M' (op + PQM.OFF_SRC) ois (ois + 16) src' ->
  PQV8.v8_at segs T3 T4 M' (op + PQM.OFF_BB) x' -> PQV8.v8_ok x' g' ->
  PQV8.vw_at (PQM.vec_owner segs A T3 T4 vp op ois lo hi s) M' src' x' g' OB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["BUpd"] "p'0h04__x1h17__arithh24__ffh37__sat10h46__sat7h56__sat8h66__sat9h78__varmaph85__with96heq_obh:1Hh;4__x2h<4__x3h=1ch>1ni001nh?1pi011ph@3HTBhA2TBhB2HahC3EOBhD3HSBhE3Hs0hF3Hs1hG2PAhH2_HhI3_H0hJ1ahK2EbhL2OBhM3_H1hN1ghO2g'hP1mi021mhQ2n0hR3srchS4src'hT1vi031vhU1xhV2x'hW3BB'hX1EhY2H1hZ2H2h[2H3h\2H4h]2H5h^2H6h_4SRC'h`4V8OKha4_H10hb4_H11hc3_H2hd3_H3he3_H4hf3_H5hg3_H6hh3_H7hi3_H8hj3_H9hk2c0hl2p0hm4p_bbi044p_bbhn4p_bgi054p_bgho7p_depthi067p_depthhp6p_donei076p_donehq6p_morei086p_morehr4p_sbi094p_sbhs4p_ski0:4p_skht5p_srci0;5p_srchu5p_stki0<5p_stkhv4p_tbi0=4p_tbhw4p_tgi0>4p_tgi0?3cntp%0p%1p&0p;2p;1p;3p;:p;6p;4p;9p;7p;5p;;p;Kp;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R0p4p710R5p1004Ep4p710R6p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R7P2p8P7P6p8P7P5p8P7P3p8P7g007_R3p4p710p8P7p1008<p4p710p8p1008Yp4p7210P6p8g00DRk20bTg0096k101Tg01kmj1~Tg00=_j3BTg01m3m:0aTg01n6j6pTg01o2j40Tg01PSl94Tg0207j2VTg00D7R6j23Tg00AUj22Tg00B2j1DTg00C<j1ITg01X1j7]Tg0213j6eTg00A9j21Tg00BWj1GTg00CZj2WTg01Amj1LTg01Uoj3lTP1j3@Tg01=Yj1ETg01>Wj1JTg01TOk20KTg01Bkk105Tg00>9k103Tg00PHj2_Tg00Y>j3vTg01UQj6tTg00YXk30CTP0k507Tg00=?k306Tg00T]k20^Tg00hQk40\Tg00ZUk10[Tg021ok40ZTg022lk30YTg023jj16Tg024jj15Tg025jj17Tg026kj4UTg027gj4cTg028dk50WTg029ej1bTg02:dj1aTg02;bj1dTg01RTl;FTg00GOk20:Tg00G3j2iTg00H7k309Tg00H[j1}Tg00I:j2|Tg00Ick308Tg00JLk20STg00KVj2{Tg00K8k10RTg00[Tj4fTg00L4k10PTg00LRk10OTg00M=j2zTg00M`j2gTg00NCk10LTg00Ofk20JTg00Pbk20ITg00QNk30HTg00Qmk40GTg00Nek104Tg00OCk30FTg01NMk40ETg02<aj6YTg01<Yj4NTg01K`k102Tg01LCk10DTg02=ej5XTg01Y6j2xTg01Z?j1yTg02>dm90BTg02?lk20MTg02A0m;0ATP3k30@Tg02B=k40NTg01;Wm:0?Tg02CBmK0QTg00Xck40;Tg00kjk40>Tg01?Uk20UTP4k30VTg00jPk30`Tg00:Tj2qTg02DWk80_Tg01@2k10]Tg00\2j4sTg00\]j7rTg00]ek800Tg00Z2k30<Tg00ilk70=Tf0R4#D#D#D#Ip=Tf2R3f1R0'2/14p=O%D4#Dp=ng00_QR1/14p==g01`TS00?B04p=\g00<DR7P7P0P4H0>p=`g01Dl00U4p=[B0V774p=oB0`774p=u1130/q4p=P%D4#Ip>0Xf6R5f5R2f4R8f3R9P3P0%b4F]p=>f7R:P5P2P8P9%E3%J0%d4L0_p=;11131104'3p=:AB751AB728'qAB791AB730'q/34'3,3:p=9P5P2P8P9P3&0]0Ee/34p=8P2P8P9P3%L0DX/34p=C1304,33,39,38p=AP5P2P8P9Cc1304,33'3p=KP8P9P3P0CU/34p=H1304,33p=SP2P8P9P3%L0DX/34,35,3:p=RP:P5P2P8P9P3P0F]/34p=mP8P9P3P0%L4DXp=^AB704p>0TP3g00_oR;g00`NR<P<g00`nR=P7P0g00aNR>P4Csg00b5R?Frp=<P9P;P<P<P=P3P0P4L00p=jP5P;P<P<P=P2P8P9P;P<P<P=P3P0P4L00L00p=h1z74p=w1z74:0<70p=MB0<704p=ZP5P;P<P<P=P2P;P<P<P=P7P8P>P9CsP?FrP3P;P<P<P=P7P0P>P4CsP?FrK0=p=Q11931104'qp=?P8P;P<P<P=P9P;P<P<P=P7P3P>P0CsP?FrP4K0=p=kg01_UR?g01aRR>20b77R;$01R@p,2OBRAp,1sRB#~RC3BRDp,4segsREp,1ARFp,2T3RGp,2T4RHp,2vpRIp,2opRJp,3oisRKp,2loRLp,2hiRMPBN:0aS01p,1MRNP5P8P3PAEpP6PEPFPGPHPIPNPJPKPBP:P2P9C0M941V29/3DPEPGp,2M'ROg010G,2JRPPKg00d;RQ#DRR#DRS#DRT#DRU#IRV,2KRWP:F]PEPGPHPOg01fV,2JRXP5Ee1V:2Q01POf:RYf8RZP5PAEp[[[P4PEPFPGPHPIPNPJPKPBf9R[P:P2C0M941VZ5/3DP61V[:PDPEPGPOPPPKPWf;R\F]PEPGPHPOPXPYEe1V\[S02Q01POf>R]f<R^PYPAEp[[[P4Q02PEPGPOPPPKPWP]F]PEPGPHPOPXf=R_Ee1V]^PEPFPGPHPIPOPJPKPBfAS03f?S04P_C0M94Q04/V_S05/3Dp,4Hlay11LJS06g00c<R`,2JRa/1MS0711LKS08%GTS09#D#TRb=OKMS0:%IRRc%nUS0;#IRU'WRd,1MS0<%=LS0='3S0>'3S0?'3S0@'3S0A'3P6Q06Q0APEPFPGPHPIPOPJPKPBfCReQ03Q04C0M94P4Q06Q0AP6Q07Q0@PEPFPGPHPIPOPJPKPBfGRffEPeC0M94P4Q07Q0@P6Q08Q0?PEPFPGPHPIPOPJPKPBfKRefIPfC0M94P4Q08Q0?P6Q0:Q0>PEPFPGPHPIPOPJPKPBfORffMPeC0M94P4Q0:Q0>P6Q0<Q0=PEPFPGPHPIPOPJPKPBfSfQPfC0M94P4Q0<Q0=%LBRfAl304Re'\S0BP@PC1`38Rg=@;4XL@P;%EBRh%JBRi+0KRj&05fRk1`09RlA@;ljA@;lkQ00Al930S0CQ00&0549@;gWTAB;ll&03;Rg9@;l1_;l3vPfP4Et40CI07A@;lCePAfUEtWKX?7X>7X=7Q0BA@;lAS0D[^?7^>7^=7P@PC1WciRj#[S0E,`hRm=@;4XL@P;B06;mgRnPkPmA@;mnA@;mkAB;mmA@;mg1_;m3v3vI07A@;mCePAfREtA@;mAp,2HAPmP4O2%omRC%umRgPL20^MLH0\S0F12CgRkp,1LS0G$0[Rn%IS=OnC3PS0H%=CS0I%=gS0J11kdS0K'3S0L'3S0M'3S0N'3P6Q0FQ0NPEPFPGPHPIPOPJPKPBfZRkfXfVC0M94P4Q0FQ0NP6Q0HQ0MPEPFPGPHPIPOPJPKPBf^Rgf\PkC0M94P4Q0HQ0MP6Q0IQ0LPEPFPGPHPIPOPJPKPBfbRkf`RCPgC0M94P4Q0IQ0LP6Q0JQ0KPEPFPGPHPIPOPJPKPBffS0OfdPkC0M94P4Q0JQ0KPCPEPFPGPHPIPNPJPKPBfjRCfhQ0OC0M94P6PEPNPJPIH0ZS0PB0YNJ`S0QPGPNPJ%GQRk#nRg$0XRnO3RoPEPN%ITRp,2JRqPBfkS0RfifgC0Rr#6RsPEPN%GS#I,2JRS%5rRtPEPN%Ig,2JRu%7rRvPEPN12JVP1CURVPEPN%GRS0S#nS0T#I,2JP1CcRRPEPFPGPN12PpRwI0WRxPEPGPNPPPKPWPrF>PEPNg01dT,2JRyg02EXRzCcR{PGPNPyPpO3R|PEPGPNg01eV,2JR}PrPEPGPHPNPXPrPEPGPHPNg01gV,2JR~PrPrPrG;PsPs%IQRsPtPtPs12zsRz9:vvG9F8ECDAFKDHDH3SPEPFPGPHPIPOPJPKPrM94P4Q0PQ0QPEPNPqPBfnS0UflPCC0RC#6RrPEPNPS%5CRvPEPNPu%7CRtPVPRPxPEPGPNPPPKPWPCF>P{P|PEPGPNP}PCPEPGPHPNPXPCPEPGPHPNP~PCPCPCG;PrPrPsPvPvPsA:ttzG9F8ECDAFKDHDH7SoP6Q0QPEPNPqPBfoS0VfmQ0RC0Rt#6RvCUPEPNPS%5tRrPEPNPu%7tRCPVPRPxPEPGPNPPPKPWPtF>P{P|PEPGPNP}PtPEPGPHPNPXPtPEPGPHPNP~PtPtPtG;PvPvPsPrPrPsA:CCzG9F8ECDAFKDH5SoPEPFPGPHPIPOPJPKPtM94P4Q0QPEPNPqPBfrS0WfpQ0UC0Rt#6RCCUPEPNPS%5tRrPEPNPu%7tRvPVPRPxPEPGPNPPPKPWPtF>P{P|PEPGPNP}PtPEPGPHPNPXPtPEPGPHPNP~PtPtPtG;PCPCPsPrPrPsA:vvzG9F8ECDAFKDH5SoP6PoPEPNPqPBfsS0UfqQ0VC0Rv#6RrPEPNPS%5vRCPEPNPu%7vRtPVPRPxPEPGPNPPPKPWPvF>P{P|PEPGPNP}PvPEPGPHPNPXPvPEPGPHPNP~PvPvPvG;PrPrPsPCPCPsA:ttzG9F8ECDAFKDHDHPEPFPGPHPIPOPJPKPvM94P4PEPNPqPBfvS0VftQ0WC0Rv#6RtPEPNPS%5vRCPEPNPu%7vRrPVPRPxPEPGPNPPPKPWPvF>P{P|PEPGPNP}PvPEPGPHPNPXPvPEPGPHPNP~PvPvPvG;PtPtPsPCPCPsA:rrzG9F8ECDAFKDHDHP6PEPNPqPBfwRrfuS0WQ0UC0RC#6S0UCUPEPNPS%5CRtPEPNPu%7CRvPVPRPxPEPGPNPPPKPWPCF>P{P|PEPGPNP}PCPEPGPHPNPXPCPEPGPHPNP~PCPCPCG;Q0UQ0UPsPtPtPsA:vvzG9F8ECDAFKDHPEPFPGPHPIPOPJPKPCM94P4PEPNPqPBfyS0UPrQ0WC0#6CUPEPNPSPBfzS0WfxS0XQ0VC0Rq#5RCPEPNPu%7qRvPVPRPxPEPGPNPPPKPWPqF>P{P|PEPGPNP}PqPEPGPHPNPXPqPEPGPHPNP~PqPqPqG;%6qRqPqPsPCPCPsA:vvzG9F8ECDAFKDHP6PEPNPSPBf{RvQ0UPrC0RC#5RqCUPEPNPu%7CRtPVPRPxPEPGPNPPPKPWPCF>P{P|PEPGPNP}PCPEPGPHPNPXPCPEPGPHPNP~PCPCPCG;%6CS0VQ0VPsPqPqPsA:ttzG9F8ECDAFKPEPFPGPHPIPOPJPKPCM94P4PEPNPSPBf}RSPvQ0UC0#5CUPEPNPuPBf~S0Vf|S0YQ0WC0RC#7RtPVPRPxPEPGPNPPPKPWPCF>P{P|PEPGPNP}PCPEPGPHPNPXPCPEPGPHPNP~PCPCPCG;%6CRqPqPs%5CRCPCPsA:ttzG9F8ECDAFKP6PEPNPuPBp+01@RtPSPvC0Rv#7RCCcPVPRPxPEPGPNPPPKPWPvF>P{P|PEPGPNP}PvPEPGPHPNPXPvPEPGPHPNP~PvPvPvG;%6vRqPqPs%5vRqPqPsA:CCzG9F8GRDAPEPFPGPHPIPOPJPKPvM94P4PEPNPuPBp+01BRuPtPSC0#7CcPVPRPxPEPGPNPPPKPWPBp+01CRSp+01AS0WQ0VC0RvF>P{P|PEPGPNP}PvPEPGPHPNPXPvPEPGPHPNP~PvPvPvG;%6vRCPCPs%5vRCPCPs%7vRv?:vzG9F8GRDAP6PVPEPGPNPPPKPWPBp+01DRvPuPtC0Ru#bP{P|PEPGPNP}PuPEPGPHPNPXPuPEPGPHPNP~PuPuPuG;%6uRCPCPs%5uRCPCPs%7uRC?:CzG9F8GRGm9SRxPEPFPGPHPIPOPJPKPuM94P4PEPGPNPPPKPWPBp+01GRup+01ES0VPSC0RS#bP{P|PEPGPNP}PSPEPGPHPNPXPSPEPGPHPNP~PSPSPSG;%6SRCPCPs%5SRCPCPs%7SRS?:SzG9F8GRGm9SRxP6PRPxPEPGPNPPPKPWPBp+01HRSp+01FPvC0RvF>P{P|PEPGPNP}PvPEPGPHPNPXPvPEPGPHPNP~PvPvPvG;%6vRCPCPs%5vRCPCPs%7vRC?:CzG9F8ECDAPEPFPGPHPIPOPJPKPvM94P4PxPEPGPNPPPKPWPBp+01KRvp+01IS0ZPuC0RuF>P{P|PEPGPNP}PuPEPGPHPNPXPuPEPGPHPNP~PuPuPuG;%6uRCPCPs%5uRCPCPs%7uRu?:uzG9F8ECDAP6PxPEPGPNPPPKPWPBp+01LRup+01JPSC0RS#bP{P|PEPGPNP}PSPEPGPHPNPXPSPEPGPHPNP~PSPSPSG;%6SRCPCPs%5SRCPCPs%7SRC?:CzG9F8GRGmPEPFPGPHPIPOPJPKPSM94P4PEPGPNPPPKPWPBp+01ORSp+01MS0[PvC0Rv#bP{P|PEPGPNP}PvPEPGPHPNPXPvPEPGPHPNP~PvPvPvG;%6vRCPCPs%5vRCPCPs%7vRv?:vzG9F8GRGmP6PEPGPNPPPKPWPBp+01PS0\p+01NRvPuC0RuF>P{P|PEPGPNP}PuPEPGPHPNPXPuPEPGPHPNP~PuPuPuG;%6uRCPCPs%5uRCPCPs%7uRC?:CzG9F8GRPEPFPGPHPIPOPJPKPuM94P4PEPGPNPPPKPWPBp+01RRuQ0\PvC0F>P{P|PEPGPNP}PBp+01SRvp+01QS0]PSC0RSPEPGPHPNPXPSPEPGPHPNP~PSPSPSG;%6SRCPCPs%5SRCPCPs%7SRS?:SzG9F8GRP6P{PEPGPNP}PBp+01TRSPuQ0\C0RuD^PEPGPHPNPXPuPEPGPHPNP~PuPuPuG;%6uRCPCPs%5uRCPCPs%7uRC?:CzG9F85S|PEPFPGPHPIPOPJPKPuM94P4PEPGPNP}PBp+01WS0^p+01UPvC0RvD^PEPGPHPNPXPvPEPGPHPNP~PvPvPvG;%6vRuPuPs%5vRuPuPs%7vRv?:vzG9F85S|P6P|PEPGPNP}PBp+01XRvp+01VPSC0RSPEPGPHPNPXPSPEPGPHPNP~PSPSPSG;%6SRuPuPs%5SRuPuPs%7SRu?:uzG9F8ECPEPFPGPHPIPOPJPKPSM94P4PEPGPNP}PBp+01[RSp+01YQ0^C0RuPEPGPHPNPXPuPEPGPHPNP~PuPuPuG;%6uRCPCPs%5uRCPCPs%7uRu?:uzG9F8ECP6PEPGPNP}PBp+01\S0_p+01ZR6PvC0RvD^PEPGPHPNPXPvPEPGPHPNP~PvPvPvG;%6vRuPuPs%5vRuPuPs%7vRu?:uzG9F8PEPFPGPHPIPOPJPKPvM94P4PEPGPNP}PBp+01^S0`Q0_P6C0D^PEPGPHPNPXPBp+01_R6p+01]S0aPSC0RvPEPGPHPNP~PvPvPvG;%6vRuPuPs%5vRuPuPs%7vRu?:uzG9F8PBg01^URuPu%~49B@APEPFPGPHPIPNPJPKP0p+01cp+01aS0bP6C0M94%L2/\eQ0D[^?7^>7^=7%E9%J9,Wc#['`=@;A%E8#=%E2%J2,Wc#[;OdPEPGPNP}P5p+01hRzp+01fS0cp+01dRCC0D^P:PzQ0cPCC0P:p+01ip+01gp+01eC0Rq#6%5q%7qPz%Lq%aqQ0cPC%Eq%Jq%dqM;F5Bu]A]F]E]D]@]G]CP4Q00g01bM$01PYP[PZP:P5P2P8P9P3P0P4M;F#~9B@APEPFPGPHPIPNPJPKP\PYP[PZP:P5P2P8P9P3P0M;Fp+028p+026p+024C0M94Q04P]P_P^P\PYP[PZP:P5P2M;FR@#L/\eQ0D[^?7^>7^=7P_P^P\PYP[PZP:P5P2P8P9M;FRq#E%Jq,Wc#['`=@;AP]P_P^P\PYP[PZP:P5P2P8M;F#E#=%E@%J@,Wc#[;OdPEPGPNP}f@R@Q04P]P_P^P\PYP[PZP:P5M;Fp+02=Rqp+02;RCp+029RzC0D^Q03P@Q04P]P_P^P\PYP[PZP:M;Fp+02>p+02<p+02:C0R\#6%5\%7\Pq%L\%a\PCPz%E\%J\%d\M;F,_uWAWFWEWDW@WGWCWuXs7Xr7Xn7Xm>Xw7WvXt?Xo7Xp7Xq7PYP[PZP:P5P2P8P9P3P0P4O;n011020001;110810710610;10=10>10410510910:10<PSQ0^Q0XPrQ0RQ0OP3O7bPPBp+01`S0XQ0`Q0_C0Rr#6%5r%7rP6%Lr%arQ0aPS%Er%Jr%drM;F9BuvPuPBQ0bP6Q0aC0R6#6S0a%56S0b%76S0cQ0X%L6%a6Q0`Q0_%E6S0d%J6S0e%d6S0fM;FS0gPEPFPGPHPIPOPJPKP4M94XPuPEPFPIPNPOPJPKP6Q0XPf%aBS0hQ0`Q0_Q0S#GS0S#n#TS0i,2JRB,_7p,2obRu00TBRBeRvPB20:ciRS1i1cR5%=i1i1j[[R:%=cRZg00d`S0jB09ci0UWBR[Q0j%=j[^BZRj20:cURY%=U1i1d[\5R5Q0jB09cU0UXBZRUQ0j%=d[^BZRZg00e<R\g00ehRz#}RC#}#},|71|7C1|7z60876087g00fG+0S&03\Rz406S0k&01\R\P7P7P71{79P9&0R7S0lCfP9Q0lCfS0mP01{73S0nCfS0o&0P7RC&0O7Rq1z71S0p1g7kR]5<qS0q&0L<R<Pq1g7TS0r9<q]S0sP<Pq1g7QRQ9<q]S0tP<Q0p=<qQCjFh20Jq=R=P4P3g00g3R]g00gSR@'_20I43=B]@dB0H710H0GR1b2b7b8X07X;7X<7%=0S0u1139S0v1193S0w%=9[[[^07^;7^<7P4PKPLPJPtQ0ZQ0]O6S0Zb1b4b5b6b3b9%=JePvPBPSP:P[PjPYP5PUPZQ0kP\P7Q0mP0P7Q0lP9Q0nCfCfS0nPCPq%GkS0l,g7Rk%wcQ0;$04S0;60F7S0m5<qS0xP<PqQ0r/Mb=<qkS0rP<Pq%Gg#D#TRg,MQRt=<qkS0yP<Q0m9<qtCjFhP=P1b2b7b8X07X;7X<7110dS0zAO9b3S0{AO3g9S0|AO9gd[[[^07^;7^<7P4PKPMPJQ0WQ0VQ0[O6S0[b1b4b5b6b3b911adRMePMeg02F[S0VPNPOPJP`H0EePJPnPvPBPSP:P[PjPYP5PUPZPzP\1{70R`PCA<qQQP=P1b2b7b8X071144^07P4PJO1RMb1b4b5b6b3b911JJePvPBPSP:P[PjPYP5PUPZPzP\P`PC%wnS0W,ZQS0}=<qtP=P1b2b7b8X07124nS0~124gRb'1^07PMb1b4b5b6b3b912JnS10/1aePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqQ0}Q09#G#TRk,MQS09PqQ0T#D#TRL,MQR@PQFQP=P1b2b7b8X07Q0~124kS11124LR]P4C?^07PMb1b4b5b6b3b9Q1012JkS1212JLS13PJC?ePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqQ0}Q0i,MQS14PqQ14Q0W'ZS15PQFQP=P1b2b7b8X07Q0~Q0i,24RL12LnS0iP4C?^07PMb1b4b5b6b3b9Q10Pu12unS10PJC?eEYPNPOPJPnCNePwQ0l#D#G#TRkPvPBPSP:P[PjPYP5PUPZPzP\P`PCQ0}%wpS0l'ZS0}9<qQP=P1b2b7b8X07Q0~/2pS0~,14^07PMb1b4b5b6b3b911JwePvPBPSP:P[PjPYP5PUPZPzP\P`PCQ0}/MkS16=<qtP=P1b2b7b8X07Q0~/2kS17/1b^07PMb1b4b5b6b3b912wkS18/1aePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqQ16Q09PqP@Q0}FQP=P1b2b7b8X07Q17Q11P]Q0~C?^07PMb1b4b5b6b3b9Q18Q12Q13PwC?ePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqQ16Q14PqQ15Q0}FQP=P1b2b7b8X07Q17PLQ0iQ0~C?^07PMb1b4b5b6b3b9Q18PuQ10PwC?eEYPNPOPwPkCNeQ0]PEQ0;$02&04T$02$0D[S0;Q0jV7V7S0jURTPOPPPKPWQ0XF]ePyPpPvPBPSP:P[PjPYP5PUPZPzP\P`PCA<qQ@P=P1b2b7b8X07114]^07PMb1b4b5b6b3b911JyePvPBPSP:P[PjPYP5PUPZPzP\P`PCQ0l,Z@RW=<qtP=P1b2b7b8X0712]pRP/1b^07PMb1b4b5b6b3b912ypRk/1aePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqPWQ09PqP@P@FQP=P1b2b7b8X07PPQ11P]P]C?^07PMb1b4b5b6b3b9PkQ12Q13PyC?ePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqPWQ14PqQ15P@FQP=P1b2b7b8X07PPPLQ0iP]C?^07PMb1b4b5b6b3b9PkPuQ10PyC?eEYPNPOPyPpCNePEPNPOP}PfPvPBPSP:P[PjPYP5PUPZQ0kP\Q0oPCPqQ0qP<PqQ0sP<PqQ0tP<Q0pQ0T#G#TRp,MQRy5<qCjFhP=P1b2b7b8X07X;7X<7Q0uQ0vQ0w129pRk#=[[[^07^;7^<7Q0Zb1b4b5b6b3b9%=}ePvPBPSP:P[PjPYP5PUPZQ0kP\Q0nPCPqQ0xP<PqQ0rP<PqQ0yP<Q0W,ZyR<Q0m5<qCjFhP=P1b2b7b8X07X;7X<7Q0zQ0{Q0|AOknd[[[^07^;7^<7Q0[b1b4b5b6b3b912}nRk/1dePfQ00Q001\9eQ0D[^?7^>7^=7PEPGPN12JpS00P0DXPNPO1x}3RP#o%uPCN]A]@P4%y9/\eQ0D[^?7^>7^=7PEPGPNQ00%y0DXP}PsPvPBPSP:P[PjPYP5PUPZPzP\P`PCA<qQyP=P1b2b7b8X07124pRp,14^07PMb1b4b5b6b3b911J}eS0[PvPBPSP:P[PjPYP5PUPZPzP\P`PC1MysRP=<qtP=P1b2b7b8X0712psRW/1b^07PMb1b4b5b6b3b912}sRs/1aePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqPPQ09A<q@yS0zDkP=P1b2b7b8X07Q1111]pS0{5PW^07PMb1b4b5b6b3b9Q12Q13/1}Rw5PsePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqPPQ14Q15=<qyRyDkP=P1b2b7b8X07Q0i/1pRP9PWL^07PMb1b4b5b6b3b9Q10/1}RW9PsueEYPNPO%y3,x}Rs#o%usCNeWAW@XQ7P4O1Al289/\eQ0D[^?7^>7^=7PEPGPNQ00Q0CDXP}PnQ0[PvPBPSP:P[PjPYP5PUPZPzP\P`PCA<q<tP=P1b2b7b8X0712pnRp/1b^07PMb1b4b5b6b3b9Re11kaePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqP<Q09Q0zDkP=P1b2b7b8X07Q11Q0{5Pp^07PMb1b4b5b6b3b9Q12=PkwePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqP<Q14PyDkP=P1b2b7b8X07APpLP^07PMb1b4b5b6b3b9APkuWeEYPNPOAl893,x}RW#o%uWCNeWAW@Xl7XQ7Xk7P3P0P4O3n011030002111003110?100101Q0UP9O2bTPNPOPJPgP}PnQ0VQ0[Pe12Jg,1keN90BQ0BQ0YP9P3P0P4O4-0MlWKX?7X>7X=7P3N;0APEPTPOP}PfDXeQ0\PEPTQ0;Q0jV7UR}POPXQ0`EeeP~PnPvPBPSP:P[PjPYP5PUPZPzP\P`PCQ0S#G#G#TRX,MQRl9<qQP=P1b2b7b8X07124XRX,14^07PMb1b4b5b6b3b911J~ePvPBPSP:P[PjPYP5PUPZPzP\P`PCQ0W,ZlRQ=<qtP=P1b2b7b8X0712XnRt/1b^07PMb1b4b5b6b3b912~nRb/1aePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqPQQ09PqP@PlFQP=P1b2b7b8X07PtQ11P]PXC?^07PMb1b4b5b6b3b9PbQ12Q13P~C?ePvPBPSP:P[PjPYP5PUPZPzP\P`PCPqPqPQQ14PqQ15PlFQP=P1b2b7b8X07PtPLQ0iPXC?^07PMb1b4b5b6b3b9PbPuQ10P~C?eEYPNPOP~PnCNeQ0RQ0d#=eQ0OQ0dQ0e,Wc#[Rc;Ode11h4Q0E,2h,i4'3Q0Gp,3LBX:0@;Ap,2spp,3scrp,1WPNPOP0p,2HPPmP0Q0UP4H0NN:0?WBXJ7PNPOPhQ0ECNePNPOQ0dPcCNeQ0^PEPFPTP}PIPNPJPKP6M94eNK0QPEPFPGPHPIPOPJPKQ0aQ0bQ0cQ0XPfQ0hQ0`Q0_PhPiQ0fM;FM94ePEPFPGPHPIPOPJPKQ0gM94ePrP4EtbXWbWAP0P4O2n2001000000121000000W:Xa|P0P4O2n2001000000121000000W:Xj{P0P4O2n2001000000121000000W:WiP0P4O2n2001000000121000000W:XhxP0P4O2n2001000000121000000W:XgRP0P4O2n2001000000121000000W:XfVP0P4O2n2001000000121000000W:WeP0P4O2n2001000000121000000W:WdP0P4O2n2011000000121000000W:WcP0P4O2n2011000000121000000W:XMoP0P4O2n2011000000121000000W:WIP0P4O2n2011000000121000000W:WHP0P4O2n2011000000121000000b:WFWMP0P4O2n2001000000121000000W:WEP0P4O2n2001000000121000000W:WIP0P4O2n2001000000121000000W:WHP0P4O2n2001000000121000000bJbDb@W^W]P0P4O2n2001000000121000000W:W\P0P4O2n2001000000121000000W:W[P0P4O2n2001000000121000000W:WZP0P4O2n2001000000121000000W:WYP0P4O2n2001000000121000000bJQ05PDP4P^H0;H0;Q01POQ03Q04P_PAEpeW`WWW_XIDWHP0P4O2n2001000000121000000W:WGP0P4O2n2001000000121000000W:WCXO7XN7XV>XU>XS?XR?P2P8P9P3P0P4O6XO7XN7XV>WUXS?WRo"). Qed.

End BUpd.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma in_lb_remove (A : Z) (LB : list (Z * Z)) b : In b LB -> fst b <> A -> In b (lb_remove A LB).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) [] "p'0h02LBh11Hh21Ah32H0h43Hneh51bi001bh62b0h71ch82IHh91ei011eh:1ni021nh;1ri031rp;2p;1p;3p;6p;5p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R3p8P0g0020R4p4p710p8P0P4p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0p1004Ep4p710R5p8p1004ap4p771111110p1005^p4p771111110p8p1006cp4p70R6P2p8P6P5p8P6P0p8P6P3p8P6p1007_p4p710p8P6p1008<p4p710p8p1008Yp4p7210P5p8g00DRj2DTg0096j1CTP1j30Tg00;kj13Tg02Gaj24Tg02Haj28Tg00>9j1:Tg00=_j35Tg00:TR1j29Tg02I@j27Tg00=?j36Tg02I]j2BTg02J?R5j2ATg00PHj2?Tg00Y>j3<Tg01UQj6=Tg00YXj3>Tg02Jbj5;TP4j3@Tg00<DR4f0R67@4p=1f1R3=546p=21D44R0#CR2P0A0036f2R7#1f4R8'2#3f3R9f5R:/47500[[X02g00>YR;%13R</29#3R=18;3W3W1%:0R;9006148;9007\=[eA0076%19/2:#3f6R=/479008[[A5079A0093'9P1A5098A0087%1:R1f7R;'2#3g00g3R>P2f8R?,71P814?8960:n0100000020000900=[P6A508:P0P=%1;R1f9R@'2RA#3P>P2f:RB,7<P=14B=R<9603n0100000020000900?[X70%1=RC/2?#3RD1B1@171@,AA%1?/7BP>P5%1@f;R5'2P>P2P3P@f=/4@RA9605n01000000200009005P3%1Bf<'2RBA005@P8P6O1'8W9P6O1%3BA5055A005A1?053<W:P6O1n10210010300021010110102b6b;W4P:P6E=W1P6O1A00:917C@P>P>P>P2P6P;145;960?n0100000020000900@P6P7A50;?A00?<P:P7P3O23>n0110000020000b6X4DW1P6O1n200100000021000010000W3A60739009%18/2=#3A6089,4;900:[[eW8X02X70P3D;X50X02X24P7P3P6O3X50W0X24o"). Qed.

Section Heap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis WFB : heap_blocks_wf L HI.
Hypothesis Herr_img : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Variables (X LBX : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps).
Hypothesis HH : hi_heap HI (X ++ LBX) cr M VM.

Lemma heapX_blk b : In b X ->
  (fst b + snd b <= hl_errno L \/ hl_errno L + 4 <= fst b) /\ 0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= hl_ceil L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Heap"] "h01Hh11bh22_Hh34__x1h44__x2h54__x3h64__x4h74__x5h84__x6h91ah:2BLh;2H0h<2H1h=2H2h>2H3h?3Hinh@2R1hA2R2hB2R3hC2R4hD2R5hE3_H0hF7__arithhG4__ffhH6__sat6hI8__varmaphJ5__withK1qhL1rp&0p;2p;3p;4p;1p;5p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0g0013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R4p8P0g0020R5p4p710p8P0P5p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R0p4p710R6p1004Ep4p710R7p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R8P2p8P8P7p8P8P6p8P8P4p8P8g007_R4p4p710p8P8p1008<p4p710p8p1008Yp4p7210P7p8g00DRk206TP1j3MTP4j3lTg02KDj3ITg02LFj3DTP5j2dj3gTP3j4bTg02MDj2aTg00D7R3j24Tg00AUj23Tg00ZUj1}Tg00B2j1?Tg00C<j1HTg00S^j1sTg00T]j2TTg00Y>j3kTP0j5iTg00A9j22Tg00U:j1eTg00V:j1cTg02MYj25Tg02N9j2`Tg02Njj2_Tg00;kj1^Tg02OKj2PTg01?Uj2]Tg00=_j3OTg02Ohk205Tg00G3j2LTg02POk203Tg02Q6k202Tg02Q\j2|Tg00H[j1FTg00I:j2CTg00Icj3NTg00JLj2[Tg00>9j1yTg00=?j3ZTg0096j1xTg00KVj2RTg00[Tj4STg00K8j1rTg00L4j1qTg00LRj1pTg00M`j2>Tg00Z2j3XTg00M=j2KTg00X@j3oTg00NCj1mTg00\2j4WTg00BWj1VTg00Ofj2jTg00PHj2tTg00Pbj2uTg00QNj3vTg00Qmj4wTg00jPj3zTg02Gaj2fTg02RBj3{Tg00:Tj2UTg00\]j7\Tg00ilj7~Tg00]Ak700Tg00]ek801Tg00<DR0f0R57g0p=0Az005p=1f3R4f2R1f1R7/f53{p=91475,41p==g00_QR8/25p=E%?5#?p=7128412811275'4'4p=<f4R6/241217'U/45p=:AD417/45p=@AO058p=;1L85p=81217/U5p=Q1317/25p=A1275,41p=G1287/45p>04P1g00_oR2g00`NR9P9g00`nR:P0P7g00aNP5CWg00b5R;F\p=6P7P2P9P9P:P5P;F\p=nP1P2P9P9P:P7P5F~p=YP1P2P9P9P:P7P5K00p=JP4P2P9P9P:P1P7P5L01p=Bf5R2/26/U412811287/45'4'4p=h20600R;p,1XR<9M;5p,3WFBp,3LBXR=9l;<R>p,2crR?p,1MR@p,2VMp,2HHO5AM;5>p,1LRA%07RB%17RC3IAD@BCPBPCPBP>C93=[^1;RBP;P01d00P>Cb,a0%0?#E%1?#E3=R?'4P3PBP?%04RC%14RD'3RE%}ARFg00d;RG#?RH#?RI#HRJ,3FRKPCPCPDPE%sARE%7IRD#7#7#7#7RC#?#7#7#7#7#7#HRL'TRMC<D:P5P7f6RNP;P<P=PNAM;N<AM;N=;k2DiO2%0NR=%1NR<5IAAD@=<P=P<P=P>C93=P3f7R=#0R<%1=RO5IAP@P<POP<POP<P>C9C@f8R<#0RO%1<RP'3RQPFPKPOPOPPPQPMC<D:P5f9RQ#0%1Q5IAP3%HCRCf:RP#0RO'2%1PRP,3ORR%eARS%cARAPO%HDRD,5O#;%8P12RM3=D:P@f;RR#0RP%1RRRPPPRPPP>C9C@f<RP#0RR%1PRP'3ROPFPKPRPRPPPOPMC<D:[P512CRf=RR#0RO%1RRR'3RPPSPAPO15OD#;%8R12PM3=D:P3f>RP#0RR%1PRO'3RT12AR7QS15RD#;%8O12TM3=P@f?RT#0RO%1TRRPOPRPOP>C9C@f@RO#0RR%1ORO'3RUPFPKPRPRPOPUPMC<D:[P512AR9QUSfARU#0RR/5D#;%1URU#8AARUM3=P3fBRU#0RR/5D#;%1URU#813RU;GMP@fCRU#0RR%1URUPRPUPRP>C9C@fDRR#0RU%1RRR'3ROPFPKPUPUPRPOPMC<D:[P515UD#;fERU#1RO#8%0U/3O;GMP3fFRO#1RU#8%0O?AUMP@fGRU#0RO%1URRPOPRPOP>C9C@fHRO#0RR%1ORO'3RVPFPKPRPRPOPVPMC<D:[P5%8OfIRO#0%1O;AMP@fJRO#0RV%1OROPVPOPVP>C9C@P3fKR3#0RV%13RO5D@PVPOPVP>C9fLRV#0RO%1VRV'3RRPFPKPOPOPVPRPMC<D:P5fMRM#0%1M5D@fNR@#0RM%1@PMP>C9fO#0R>/`D%E>%EDfQ#0R>/5DRM#E[[fP#0/_D%;DR@#^1P>D,]D/3M9O0>[205>D%8DfR#0R>/5DRM1LMD+04[203>D1LD8fS#0R>/5DRM,LD?GM8[202>DfT#0R>/PD#;\@1|>DfU#0R>/5D=O0>\@1P>DP0fV#0/5DP0g00e<RDg00ehR>#FR@#FRM#FRR#F#F,C0RV1C0M1C0>5N05N0g00fGR>'[1C0R1C0@5N09N0V/[>%yD5ZD3Z%xDP0P01R06P11R0NCSP7P01R02P4%r0CSCS%q0%p0R61>0GRD1>0HR>5X0RV1>0I1K0L5o0566RI%m9R9P6P01K08R@g00bUP>CW,n6P9P6%VH,>0RH966V%VGRG#?,>0RR=66D5Y6P9P61K0C=66DP9P61>0GRG966H1K0J9X0GRH=66R5J6P9A66VGA66HD5Y6A66@DA66@>=J6I5J65J6CBCBCBCBCB1j6:P5P1g00g3R6g00gSR:'t1u51=O6:dAv087CwbGbIbJX30X40X50X60X70X801T4L9A57%81131412=17QN12C412<N13NJ;GQ132NRQP=AA=J2P2PN1T<L,2QEh[[[[[^30^40^50^60^70^80P5PAPSPEPFfXRF#1%0FPPPTPUP3p,8Herr_imgO;bFbLbKb>b=b<b;b0bHWEW2P7P5O2n2001000000121000000W0WDWCP7P5O2n2001000000121000000W0WBP7P5O2n2001000000121000000W0WAP7P5O2n2001000000121000000W0W@P7P5O2n2001000000121000000W0P7P5O2n2001000000121000000b9X2?X:BP7P5O2n2001000000121000000b9W?X1;P5O1W1o"). Qed.
Lemma heapX_nodup : List.NoDup (map fst X).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Heap"] "h02NDh11lh21Hh32_Hh43_H0h51ah61bp;2p;3p;4p;1p;5p;6p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0g0013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R4p8P0g0020R5p4p710p8P0P5p4p7210p8p1002Mp4p70p1003Jp4p7210p8p100<bp4p710R0g004ER6p4p710R7p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R8P2p8P8P7p8P8P0p8P8P4p8P8g007_R4p4p710p8P8p1008<p4p710p8g02SER8p4p7210P7p8g00DRj2CTP4j37TP1j3;TP5j34j28Tg00jPj35Tg02KDj3ATg02LFj3<Tg02Gaj2:Tg02RBj39Tg00D7R5j20TP3j43Tg02MDj22Tg00A9j26Tg01Foj21Tg0096j1BTP8j5@TP6j6=Tg02Saj2>Tg02T>j4?Tp,3WFBg00<DR6/C6R8p,1XR3p,3LBXR137R4p,2crR7p,1MR0p,2VMp,2HHO5f0R2=;84p,1Lf1R99466R:A5669R;3AA<0:;1::499:;'0'0[^68R;P8P61866R:P4C3R4,26R0g00_QR<A4667'6A5667,6<'0R<'0R7'0P5P;P7P8P6P:P3C3R=,16R>P2P5P0P<P>P2%B6R>P41262R4X1>P9P8P6P:P1C3R?976=R@P8P6P:P3P1D@E=126@P51169\4R411621269R5[f2,16\51>62P9n2001000000120000000X1>P4^1>P2P@P9O2116@P6P=P?P2C?b0b2b0X4<X00P9P2O2n2001000000120000000X27X3;P9P2O2n2001000000121000000b5o"). Qed.
Lemma heapX_apart b1 b2 : In b1 X -> In b2 X -> fst b1 <> fst b2 -> apart (fst b1) (snd b1) (fst b2) (snd b2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Heap"] "h01Hh12_Hh24__x1h34__x2h44__x3h54__x4h61ah72b1h82b2h92APh:2BLh;1Eh<2H1h=2H2h>3Hneh?3_H0h@7__arithhA4__ffhB8__varmaphC5__withD1bp;2p;3p;1p;4p;5p;7p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0g0013R3p4p710p8P0P3p4p7210p8P0p1001Op4p710R4p8P0g0020R5p4p710p8P0P5p4p7210p8p1002Mp4p70p1003Jp4p7210p8g00h3R0p4p710R6p1004Ep4p710R7p8p1004ap6067111111004p1005^p4p771111110p8p1006cp4p70R8P2p8P8P7p8P8P6p8P8P4p8P8g007_R4p4p710p8P8p1008<p4p710p8p1008Yp4p7210P7p8g00DRj2^TP1j38Tg00=_j3=Tg00;kj1]TP4j3PTg02KDj39Tg02LFj35Tg02Gaj26Tg02RBj34Tg00D7R4j22TP5j2Fj3WTP3j4\Tg02MDj2UTg00A9j23Tg00hQj4;Tg00Y>j3DTP0j5BTg01Gnj4OTg02Tej5NTg00AUj27Tg00:Tj2<Tg00>9j1MTg0096j1LTg00KVj2@Tg00K8j1KTg00[Tj4?Tg00L4j1ITg00LRj1JTg00M`j2:Tg00B2j1>Tg00Z2j3ATg00BWj1HTg00\2j4CTg00ilj7GTg00NCj1QTg00]ej8RTg00Ofj2STg00PHj2[Tg00Pbj2ZTg00QNj3YTg00Qmj4VTg00jPj3XTg00\]j7TTg00<DR0f0R37W0p=0AX003p=1f1R5g00_oR1g00`NR7P7g00`nR8P3g00b5FTp=E1^00R6p,1XR29865R9f3R:#0f2R;#05=0#]p,3WFBp,3LBXR<9P62R=p,2crR>p,1MR?p,2VMp,2HHO5A863=p,1LR@%05RA%15RB39A5?AB16A=94AB'2'2[^D6RBP6P01F00P=C\,U0g00_QRA%0>'3%1>,3A'2'2R>'2P4PBP>f6RC#0%1Cf5RC#0%1CC;P3P5f9RCP6P2P<PCA86C2A86C<f73DDBO2%0CRD%1CRC59@A5?DC16D=94DC'2'2P4f:RC#0RD%1CRC59@A5?DC16D=94DC'2f;RE#0%1EPDPCC;P3f<RC#0%1C59@f=R@#0RC%1@R@55?16C=94C@'2P4f>R4#0R@%14R455?16@=94@4f?RC#0%1CP@P4C;P3f@R4#0%1455?fAR?#0R4%1?R@164=34P3P?fBRD#0REP=P?P6P2P<P?A86?2A86?<;DCDBA=04EPCP0PEfCRC#0R?P3COO1W;DNO2%1DRD,7E/34174@/3E'<g00e<R@#M%L@P0P0f4R@,@0P;%K0C?P51@0:C?%I0%J0R4P1P7P7P8P4P1P7P7P8P0g00d;R1,:0R<%>1R2,:05A0g00aNR=%H1,:0R1CC,E4P0%>2,:09A01P=P<CC,E4FGR<%Q7P<GR1S48P3P;g00g3R4g00gSR8'[1Z3;==48dAY0A5CVbAbBbCX20X30X40X501735/3;17;:/33'<175;/3:17:@/35'<[^20^30^40^50P3%1CRCP?fDR0#1%00P5O5b@P?PCPEPDC;eb0W9W?P5P3O2n2001000000121000000W0W1P5P3O2n2001000000121000000b6X1>X:BP5P3O2n2001000000121000000b6W>X=9W<X86X76P5P3O2X86W7o"). Qed.
End Heap.

Section Owners.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis WFB : heap_blocks_wf L HI.
Hypothesis Herr_img : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Variables (op ois lo hi : Z) (s : PQM.mpst).
Hypothesis Hceil : hl_ceil L <= lo.
Hypothesis Herr : hl_errno L + 4 <= lo.
Hypothesis Hlay : lo <= op /\ op + PQM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= hl_sptop L /\ hi <= 2 ^ 47 /\ 4096 <= lo
                  /\ op mod 8 = 0 /\ ois mod 8 = 0.
Hypothesis Hdis : op + PQM.PSIZE <= ois \/ ois + 272 <= op.

Abbreviation SO := (PQM.src_owner segs A PMSP.T3 PMSP.T4 vp op ois lo hi s).

Theorem src_owner_ok : PGS.owner_ok segs A L HI SO.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Owners"] "p'0h01Hh14__x1h24__x2h31rh44__p1h52H0h63H10h73H11h83H12h93H13h:3H14h;3H15h<3H16h=3H17h>7__arithh?7__sat10h@7__sat11hA7__sat12hB7__sat13hC1qhD2q0hE2r0hF4__ffhG8__varmaphH5__withI4__p2hJ4__p3hK4__p4hL1bhM4__p5hN1BhO4__p6hP4__x3hQ1mhR4__p7hS4__x4hT3HAfhU2HHhV2HPhW2HahX2OBhY4__x5hZ4__x6h[3H18h\3H19h]3HBch^3HCxh_1Mh`7__sat14ha3srchb3HOWhc3Hinhd4__p8he4__p9hf7__sat15hg4__x7hh4__x8hi4__x9hj1lhk2r1hl1xhm1Dhn2E1ho2E2hp2E3hq2E4hr3EOBhs2Fbht2H1hu2H2hv3H20hw3H21hx3H22hy2H3hz2H4h{2H5h|2H6h}2H7h~2H8i002H9i013HQCi024HSRCi032Hbi043Hb1i053Hb2i062Hfi072Hii083Hnei093Hspi0:3LBXi0;2M'i0<2NIi0=2PAi0>3SRCi0?2VMi0@2Wxi0A2_Hi0B3_H0i0C3_H1i0D3_H2i0E3_H3i0F3_H4i0G3_H5i0H3_H6i0I3_H7i0J1ai0K2b1i0L2b2i0M2cri0N1ii0O1ki0P5lemmai0Q1pi0R2q1i0S3scri0T2spi0U4src'i0V1zp%0p%1p&0p&1p;2p;1p;:p;5p;4p;3p;6p;7p;<p;9p;>p;Mp;;p;8p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0g001OR3p4p710R4p8P0g0020R5p4p710p8P0P5p4p7210p8g002MS00p4p70p1003Jp4p7210p8g02UmR0p4p710R6g004ER7p4p710R8p8p1004ap6067111111004p1005^p4p771111110p8g006cS01p4p70R9P2p8P9P8p8P9P6p8P9P4p8P9g007_R4p4p710p8P9g00?6R9p4p710p8p1008Yp4p7210P8p8g00A9j22Tg00B2j1CTg00BWj1YTg00C<j1ITg00AUj21Tg00S^k10uTg00CZk20TTg02MYj2kTg00D7R8j20Tg02VKm:1JTg02WNk51GTg00Nek10?Tg01K`k10_Tg01LCk11:Tg00DRS02k20}Tg0096k10GTg02XOj4oTg01OQj24Tg00lJk10tTg00=_j36Tg02YKk10qTg02ZGk10nTg021ok40RTg022lj3fTg02[DR6j3lTg023jj19Tg024jj18Tg025jj1;Tg026kj4cTg027gj4jTg00G3j27Tg00GOk20WTg00H7k30VTg02N9k20ITg02Njk20FTg00;kk104Tg02OKk20ETg01?Uj2uTg02Ohk20DTg02POk20CTg02Q6k20ATg02Q\k20@Tg00>9k10sTg00K8k10rTg00L4k10pTg00LRk10oTg00M`k20STg00Ofk20mTg00PHk20lTg00Pbk20kTg00QNk30jTg00Qmk40iTg01Lek20QTg00NCk10PTg00M=k20OTP7k60=Tg02\@k10hTg02\^k20gTg00H[j1TTg02]?k30<Tg00I:k20MTg00JLk20LTg02]hk20KTg00=?k30;Tg00^mk60fTg01ITk30:Tg02^Tk11ITg02_Pk11HTP4j3HTg02`Lj5{TP3j3dTP1j3ZTg00jmj1zTg00kjk40dTg02aJk60cTg00:TS03j2XTg02bGj3yTg01QWj7pTg00nJk100TP0k40aTg00OCk30`Tg00Xcj4qTg02cDm<1FTg00ZUk11ETg00T]j2sTg00hQj4QTg00?Xk21ATg00@1k31@TP9k31?Tg00X@k30UTg02dIm91>Tg02ePm>1=Tg011Hk61<Tg02fWmM19Tg01UQm;18Tg02g`k315Tg02h]m911Tg01PSm910Tg028dk506Tg01X1k707Tg01=Yk10~Tg01>Wk112Tg02;bk10|Tg02DWk813Tg01@2k114Tg0213k60{Tg01Amk116Tg02=ek517Tg029ek10^Tg00KVk20zTg00[Tk41;Tg00Z2k30yTg00\2j4vTg00\]j7xTg00]Ak70JTg00]ej8rTg00^Ik60xTg00Ick30wTg00ilk71BTP5k31CTg00jPk30vTf2R5f1R9'1f0R0'2p=L%C0#C#C#Cp=}%C0#Cp>01g00<DR1g00_QR3760p=Of6R4f5R7P6g02i^R2f4R:f3R;P5P9P0N910p=mP4P7P6P:P;I06Af590'0p=UP4P6P7P:P;P5P9K07/00p=R12351290'0p=5A6143A617:'XA61;3A6159'X/00'0p==P4P6P2P7P:&0~;&125&0|9L13/00p=<P:P6P2P;P5&149J0{/00p=@P:P6P;P5&169I17/00p=?P4P7P:g02EXR<CjAl;59/00'0p=>P4P6P7P:P;P5&0^9K07/00p=Ff7R=P4P7P3CjP:P;P6P5P9I06/00'0p=SP=P4P7P:CjP;P5P9P3Cc/00'0p=\P:P;P5P9Cc/00p=M1090,05p=NAl;59/00p>0bP:P;P6P5P9I06/00p>02P4P7P:P3CcP;P5P9P3Cj/00'0p>0\P5P9P0P3Ccp>0[P5P9P0P3Cjp>0ZP;P5P6P9P0I06p>0HP7P6P:P;P5P9&0^0K07p>0YP7P6P:P;P5P9P0K07p>0X1230p=311909615p=b1290,05p>0BA6190p=t20z10p=`P1P5P9P0H1;p=K20O10p=_20S10p=WB0y190p=EP5g00_oS04g00`NR>P>g00`nS05P1P9g01K9R?P0Cvg00b5R@Fxp=h1239/00p=eP1P9g00bUP0Cvp=~P5Q04P>P>Q05P1P9g00aNRAP0CvP@Fxp=GP9Q04P>P>Q05P0P@Fxp>0>P5Q04P>P>Q05P9P0K0Jp=iP;Q04P>P>Q05P5P9P0Grp=AP:Q04P>P>Q05P;Q04P>P>Q05P5P@FxP9P0Grp>0NP4P7P:P;P5P9P0CqCqp=a12;51290'Xp=:P9Q04P>P>Q05P0J0xp=^P:Q04P>P>Q05P;P5Q04P>P>Q05P9P0K0JK0Jp=J1090,05,0;,0:p=g20M10p=]B0w190p=VP7Q04P>P>Q05P:Q04P>P>Q05P1P;PAP5CvP@FxP9P0Grp=[P1P9P?P0Cvp>0eP4Q04P>P>Q05P7P:P;Q04P>P>Q05P5P9P0GrGrp>031259/00p>09P5Q04P>P>Q05P9P0K1Bp=w1290,X5p=n12:;1259/00'0p=|&009=H50p=PB1C110p=BB0v110p=D1259/X0p>08AH5909H:;p>051X;51239/00'0p>1D1X59/00p>0]p,4HlayS06p,2loR?p,2opR@'2S07g00c<RAp,2hiRB5L@S08p,3oisRC,2?S09g00d;S0:#CRD#CS0;#CRE#Y#}#IS0<,1CS0=/2BS0>p,1LS0?$0uS0@,2BS0A%IDS0B%YDRF#YS0C#Y#YS0D#IRG+0TS0E,2BS0F%CERH$01S0G$01#}S0H#IS0I/2?S0J%IERI,k@RJ#OS0K1kCIRK#OS0L'0S0M'0S0N'0S0O'0S0P'0S0Q'0S0R'0S0S'0P8Q07Q0Sp,4segsRLp,1ARMQ0?p,2HIS0TPLPMP6P2p,2vpS0UP@PCP?PBp,1sR2N:1JS0VI1GR6P0Q07Q0SP8Q08Q0RP6P0Q08Q0RP8Q09Q0QP6P0Q09Q0QP8Q0>Q0PP6P0Q0>Q0PP8Q0AQ0OP6P0Q0AQ0OP8Q0FQ0NP6P0Q0FQ0NP8Q0JQ0MP6P0Q0JQ0MP8Q0KQ0LP6P0Q0KQ0LPLPMQ0?Q0TQ0VQ0G$0?S0W$0_&0?E$0_S0X$1:S0Y[S0Zg01_US0[20}11RE$0GR6Q0VP5P9P0CoP8PLPMQ0UP;P@PC1425Fm&0t2RN9669PLP:Q0V$0qROQ0V$0nRP%IHRH,1PS0\P;PLPMP:11OIRQP:POQ0;#YS0]#C#Y#C$01#IRRFUFRP0PLPMQ0UP7P@PC142:FmP8PLP4P@Q0UH0RAf4@AQ0:#YS0^#CS0_#CS0`#C#IRS9l4@PLP411@IRT1427RU#9RVPLP4Q0]#I,1@RW%8URXPLP4Q0`#I,1@RY%;URZPLP411@HR[PLP4%CFS0a#C#I,1@RFPLPMP4g010G,1@R\/1IR]PLP4P\PC11CHRHPUPLP4g01dT,1@R^P4P^PIPLP4g01eV,1@R_PUPLP4g01fV,1@R`PUPLP4g01gV,1@RaPUPUPUPVPVQ0:#IRVPXPXPV11<VR<95ZZF=F<D@D?F>FFGSG\DMDM3NA667NPLf8RZPOPPQ0\P=PLPMPZPQPZPOPRFUFR[P0PLPZP@Q0UH0Rf9RX?f@AAlX@SPLPXPT142ZRU#9RbPLPXPW%8URcPLPXPY%;URdPLPXP[PLPXPFPLPMPXP]PLPXP\PCPHPUPLPXP^PXP^PIPLPXP_PUPLPXP`PUPLPXPaPUPUPUPbPbPVPcPcPVA5dd<F=F<D@D?F>FFGSG\DMDM3NP8f:Rd?f@APdP@PSPLPdPT142XRc#9RbPLPdPW%8cRUPLPdPY%;cRePLPdP[PLPdPFPLPMPdP]PLPdP\PCPHPcPLPdP^PdP^PIPLPdP_PcPLPdP`PcPLPdPaPcPcPcPbPbPVPUPUPVA5ee<F=F<D@D?F>FFGSG\DMDMH0bA66XNPLf<RePOPPQ0\f;S0bPLPMPePQPePOPRFUFR[P0Afe@Af=RAP@PSPLPAPT142eRU#9RbPLPAPW%8URcPLPAPY%;URfPLPAP[PLPAPFPLPMPAP]PLPAP\PCPHPUPLPAP^PAP^PIPLPAP_PUPLPAP`PUPLPAPaPUPUPUPbPbPVPcPcPVA5ff<F=F<D@D?F>FFGSG\DMDMH0bP8f>Rf?l@SPLPfPT142AS0c#9RcPLPfPWQ0c#8RbPLPfPYQ0c#;RUPLPfP[PLPfPFPLPMPfP]PLPfP\PCPHQ0cPLPfP^PfP^PIPLPfP_Q0cPLPfP`Q0cPLPfPaQ0cQ0cQ0cPcPcPVPbPbPVA5UU<F=F<D@D?F>FFGSG\DMDMA66ANPLf@S0dPOPPQ0\f?S0ePLPMQ0dPQQ0dPOPRFUFR[P0Q0d?l@SPLfAS0fPTQ0d,42S0g#9RUPLQ0fPWQ0g#8RbPLQ0fPYQ0g#;RcPLQ0fP[PLQ0fPFPLPMQ0fP]PLQ0fP\PCPHQ0gPLQ0fP^Q0fP^PIPLQ0fP_Q0gPLQ0fP`Q0gPLQ0fPaQ0gQ0gQ0gPUPUPVPbPbPVA5cc<F=F<D@D?F>FFGSG\DMDMP8PLfBS0hPTQ0f,42Rc#9RbCcPLQ0hPW%8cRUPLQ0hPY%;cRgPLQ0hP[PLQ0hPFPLPMQ0hP]PLQ0hP\PCPHPcPLQ0hP^Q0hP^PIPLQ0hP_PcPLQ0hP`PcPLQ0hPaPcPcPcPbPbPVPUPUPVA5gg<F=F<D@D?F>FFGSG\DMQ0f=66NPLfDRgPOPPQ0\fCS0iPLPMPgPQPgPOPRFUFR[P0PLPgPTQ0i,42#9CcPLfERTPW142gRU#8RbPLPTPY%;URcPLPTP[PLPTPFPLPMPTP]PLPTP\PCPHPUPLPTP^PTP^PIPLPTP_PUPLPTP`PUPLPTPaPUPUPU%9URUPUPVPbPbPVA5cc<F=F<D@D?F>FFGSG\DMP8PLfFRcPW142TRb#8RUCcPLPcPY%;bRhPLPcP[PLPcPFPLPMPcP]PLPcP\PCPHPbPLPcP^PcP^PIPLPcP_PbPLPcP`PbPLPcPaPbPbPb%9bRbPbPVPUPUPVA5hh<F=F<D@D?F>FFGSG\A66TNPLfHRhPOPPQ0\fGS0jPLPMPhPQPhPOPRFUFR[P0PLPhPWQ0j,42#8CcPLfIRWPY142hRU#;RbPLPWP[PLPWPFPLPMPWP]PLPWP\PCPHPUPLPWP^PWP^PIPLPWP_PUPLPWP`PUPLPWPaPUPUPU%9URiPiPV%8URUPUPVA5bb<F=F<D@D?F>FFGSG\P8PLfJRbPY142WRU#;RiCjPLPbP[PLPbPFPLPMPbP]PLPbP\PCPHPUPLPbP^PbP^PIPLPbP_PUPLPbP`PUPLPbPaPUPUPU%9URjPjPV%8URUPUPVA5ii<F=F<D@D?F>FFI02K0\A66WNPLfLS0kPOPPQ0\fKS0lPLPMQ0kPQQ0kPOPRFUFR[P0PLQ0kPYQ0l,42#;CjPLfMRYP[PLPYPFPLPMPYP]PLPYP\PCPHQ0k,42RiPLPYP^PYP^PIPLPYP_PiPLPYP`PiPLPYPaPiPiPi%9iRUPUPV%8iRUPUPV%;iRi?5i<F=F<D@D?F>FFI02K0\P8fNS0m>0[L[PLQ0mPFPLPMQ0mP]PLQ0mP\PCPH142YRiPLQ0mP^Q0mP^PIPLQ0mP_PiPLQ0mP`PiPLQ0mPaPiPiPi%9iRUPUPV%8iRUPUPV%;iRi?5i<F=F<D@D?F>FFGSA66YNPLfPS0nPOPPQ0\fOS0oPLPMQ0nPQQ0nPOPRFUFR[P0Q0n>0[L[PLfQR[PFPLPMP[P]PLP[P\PCPHQ0n,42RiPLP[P^P[P^PIPLP[P_PiPLP[P`PiPLP[PaPiPiPi%9iRUPUPV%8iRUPUPV%;iRi?5i<F=F<D@D?F>FFGSP8fRRi>0ZLFPLPMPiP]PLPiP\PCPH142[RUPLPiP^PiP^PIPLPiP_PUPLPiP`PUPLPiPaPUPUPU%9URiPiPV%8URiPiPV%;URU?5U<F=F<D@D?F>FFI02A66[NPLfTR[POPPQ0\fSS0pPLPMP[PQP[POPRFUFR[P0B0ZL[FPLPMfUS0qP]PLQ0qP\PCPH142[R[PLQ0qP^Q0qP^PIPLQ0qP_P[PLQ0qP`P[PLQ0qPaP[P[P[%9[RFPFPV%8[RFPFPV%;[R[?5[<F=F<D@D?F>FFI02P8PLPMfVR[P]H0HPLP[P\PCPHQ0q,42RFPLP[P^P[P^PIPLP[P_PFPLP[P`PFPLP[PaPFPFPF%9FR[P[PV%8FR[P[PV%;FRF?5F<F=F<D@D?F>FFQ0q=66NPLfXS0rPOPPQ0\fWS0sPLPMQ0rPQQ0rPOPRFUFR[P0PLPMQ0rP]H0HPLfYS0tP\PCPHQ0r,42RFPLQ0tP^Q0tP^PIPLQ0tP_PFPLQ0tP`PFPLQ0tPaPFPFPF%9FR[P[PV%8FR[P[PV%;FRF?5F<F=F<D@D?F>FFP8PLfZRFP\PCPHQ0t,42R[J0YPLPFP^PFP^PIPLPFP_P[PLPFP`P[PLPFPaP[P[P[%9[RFPFPV%8[RFPFPV%;[R[?5[<F=F<D@D?F>Q0t=66NPLf\R[POPPQ0\f[RFPLPMP[PQP[POPRFUFR[P0PLP[P\PCPH142FJ0YPLf]RFP^PFP^PIPLPFP_142[R_PLPFP`P_PLPFPaP_P_P_%9_RaPaPV%8_RaPaPV%;_R_?5_<F=F<D@D?F>A66[NPLf_S0uP\PCPHf^S0vJ0XPLPMQ0uP]H0HR]Q0u?f\RS0w'0P5P]Q0wP4%30S0x170RS0y'0Q0B00WGR]Q0B,73S0z%3GQ0E,73[[RHQ0B#3S0{g00d`S0|Q0B@0VG9UWWRGQ0{Q0|Q0E#3[]WR[20I@IR_%3@%3IS0}%3JR<[[RV20ICIRa%3CQ0}%3KRF[[R`20FCIR^%OIS0~$04S1020ECIRU,uI=bCK[Ri20DCIRj173IS1117KI,0F[RF20CCIRk17I3S1217IK@0BK3[Rl20ACIRmQ0~%OU[Rn20@CIRoQ0~1tKC[RpPUP1PKP120F@IRqQ1020E@IRr,uI=b@J[Rs20D@IRtQ1117JI,0<[R<20C@IRuQ1217IJ@0BJ3[Rv20A@IRwQ0~%Or[Rx20@@IRyQ0~1tJ@[RzPrP1PJP1P8Q0i#3Q0i/7R11Sg,1@11@SR{;bgQ0h%3T17cRg00e<S13$0sR|Q13$0GS14%`5S15&0r1S167K9S17&0p1S18&0o1R}Q0:-0S1R~%_SS19%WDS1:'E'EQ19,E~S1;Q1:'E3hQ05-0m}S1<P0P5g00g3S1=g00gSRD+0lQ1=20k05;6DdB0j139H0iS1=bFbGbHX11X2111S9RD,10110S;b9^11^21P0PhP@O2b>W\W[P9P0O2n2001000000120000000bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbB11@D?b{9P111S5S1>,1@Q0YfcQ0W00Q0O1Q0X$0PS0X36$04Z0V1Q0qQ1>P]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P8%3g17gR11STRDQ0`#Y#}#IS1?,7D'eQ0i%3cQ0j/7RP|Q14%`9S1@Q18P}P}%_RS1A,~~&0P>RDP}20O13S1B=G}~S1CPDQ1BQ19/E~S1D5G}Q1DQ1?#_S1E'~-0>}5i}CAI0NQ1<Q1=bFbGbHX11Q0y%39S1DQ1>Q1>Q1?'7'e[[^11P0PWP9P5O3b>W\W[P9P0O2n2001000000121000000bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBO211{5P0J0=b0Q0YfaQ0W11\9+0QO1Q0X36$04eY07Z0N1Q0weFaPLQ0uPOPPQ0\Q0vPLPMQ0uPQQ0uPOPRFUFReY0IY0HY0>P9P0O2n2001000000121000000W0Y0<P9P0O2n2001000000121000000W0Y0GP9P0O2n2001000000121000000W0Y0FP9P0O2n2001000000121000000W0Y0EP9P0O2n2001000000121000000W0Y0DP9P0O2n2001000000121000000W0Y0CP9P0O2n2011000000121000000W0Y0BP9P0O2n2011000000121000000W0WmP9P0O2n2011000000121000000W0Y0AP9P0O2n2011000000121000000W0P9P0O2n2001000000121000000W0WXWaW_12?{11{RRQ/2BS0uQ09Q0>Q0A1k{IS0v#OS0wQ0LQ0JPQPCQ0=P{C:S0X'0S0Y'0S0y'0S1>'0S1F'0S1G'0S1H'0P]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1p-0RQP|Q14Q17Q18P}Q1:9G}~S1I1^}:S1J5i}S1KPDQ1:Q19'E9G}~CAQ1<Q1=bFbGbHX11X21W41209S1L/05S1M115S,29[^11^21^4QP0Q1?=L@BS1NQ09Q0>Q0AQ0FQ0J%O9S1O%OZ'0S1P'0S1Q'0S1R'0S1S'0S1T'0S1U'0P@P?Q06O4S1Vb>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ0uQ1HP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}P}Q1JP}Q1E,E~Q1:5G}S1E1^}7S1HDJS0uPDQ1;Q1A'EQ1:5G}S1ACAQ1<Q1=bFbGbHX11X21X4QXIQQ1?=L09S1W=N5;S1X119SS1Y?LR5S1Z[^11^21^4Q^IQP0Q1UQ07PBP@Q06O5S1Ub>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ09Q1GP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}P}Q1JP}Q1HQ1I1^}4S1G5i}DJPDQ1ICAQ1<Q1=bFbGbHX11X21X4QXIQXJQQ1L/0:9N5;1295S1[[^11^21^4Q^IQ^JQP0Q1TQ1NQ07PCP?Q06O6b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBS1TQ0>Q1FP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}P}Q1JP}Q1HP}Q1GP}Q0<#_S1F,E~Q1:5G}S1\1^}=S1]DJDJPDQ1\CAQ1<Q1=bFbGbHX11X21X4QXIQXJQXKQP5P;P:Q0<=L09P7DgQ0<,19S1\/25[^11^21^4Q^IQ^JQ^KQP0Q1SQ09Q1NQ07PBPCQ06O7b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBS1SQ0AQ1>P]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}P}Q1JP}Q1HP}Q1GP}Q1]Q1I1^}ZS1>5i}DJDJPDQ1ICAQ1<Q1=bFbGbHX11X21X4QXIQXJQXKQXMQP5P;P:P7Q1L/04DgQ1[[^11^21^4Q^IQ^JQ^KQ^MQP0Q1RQ0>Q09Q1NQ07Q0@PBQ06O8b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ0wQ0yP]PHPGP[P_PV20I{I%3{Q0}Q0v#3S0y[[PaP`20F{IQ1020E{IS0w,uIQ0v5b{[20D{IQ11Q0yQ0v/7I'0[20C{IQ12Q0v,7IQ0v<0B3[20A{IQ0~Q0w#O[20@{IQ0~Q0v/t{[Q0wP1Q0vP1P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1Q13Q0:$0h-0g1R{g00ehS0:#TS0v#TS0w#TS12#TS0y#TS10#T#TS1R#TS1L#T#T#TS1^#]60<1Q1L#]S1LQ1R#]Q0y#]S0y:0<1{'V'V'VQ1^#T#]Q1L:0<1{Q10#]S10Q0v#]R{'V'V'VQ0:-0M1,V{S0:g00fGS0v+0L+0K+0KR{Q13@0;{|40;Q14Q16%`=7KX%`7S1L%`X7K57KX%`:S1^%`Z7KX%`4S1RQ167K;7KX7K9Q18P}P}P}Q04P>P>Q05%_IR>Q1B5h}J0fS05PDQ0^#YR{#WS04%C{#W:0:1>Q0a#WS0a'E5h}CAPDP}P}Q05PDQ0]#WS0]Q0_#Y#W:0:1>Q0C#WS0C'E5h}CAPDP}P}Q1B/~>-0>}S1_PDQ1C1~~>-0>}5i}CAPDP}P}Q05PDQ04Q19'ER{Q0`#W:0:1>/E~5h}CAPDP}P}P}Q1BP{PDP}P}Q1BP>PDQ1CE[E[PDP}Q0CQ1B5h}PDP}P}Q0aQ1B+0ePDP}P}Q0I#_S0`Q0_#WS0_PDP}P}Q0_Q0]PDP}P}Q0_Q04PDQ1B9h}~S1BE[E[E[I0NK03K03K03Q1<Q1=bFbGbHX11X21XP1XS1XY1XZ1Xg1Xh1Xi1Q0~g00>YS0][R>1uIXR{=b;7[Ab7{=\>Q11%3;S0~17;I'0[114SRS1uId;b:\>%3SQ0}%34[[%OdRSQ0I/2ZQ0b,2XQ0b,2dPS[[[\S[[[[[[^11^21^P1^S1^Y1^Z1^g1^h1^i1P0P5PXQ0dPZP9PCP@P?Q0eP=PfPgPTQ0jQ0lQ0kQ0nf`fhOCb>bkc0Rbxbwbvb\b[bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBb`Q0LQ0YP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q1@Q18P}P}Q1_PDQ1C1^};S1_5i}CAPDP}P}Q1JP}Q1HP}Q1GP}Q1]P}Q1>P}1^}XRSP}1^}dP}Q0b,^}Q1BDJDJDJDJPDQ1BK03Q1<Q1=bFbGbHX11X4QXIQXJQXKQXMQXOQXRQXdQXeQQ11Q1D/05[P;P:P7P4P=PZPXPdQ1ODgDg%O5[[^11^4Q^IQ^JQ^KQ^MQ^OQ^RQ^dQ^eQP0Q1OQ0JQ0FQ0AQ0>Q09Q1NQ0717ZIPZPAQ06O<b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ0JQ0XP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q1@Q18P}P}Q1_P}Q1JP}Q1HP}Q1GP}Q1]P}Q1>Q0`=G}~R>=i}SDJDJDJS0`PDP>CAQ1<Q1=bFbGbHX11X4QXIQXJQXKQXMQXOQXRQP9P5P;P:Q0I@090=9N74DgS0XQ0I/29[^11^4Q^IQ^JQ^KQ^MQ^OQ^RQP0Q1PQ0FQ0AQ0>Q09Q1NQ07P?Q06O9S1Pb>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}Q1EQ1:Q1F'ER>=G}~5w}PDQ1AQ1;9G}>5w}CAQ1<Q1=bFbGbHX11X21Q1WQ1\;n0Q1ZQ0<,15Q1Y3n[^11^21P0PCP@p,4HdisS1ZO3b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBFaFaFaFaP?P\11\RR>PBQ09Q0>Q0A1k\I#OQ0LQ0JP>PCQ0=P\C:3NDgD|eQ0V$1IS0=PO11ORS1YQ0V$1HS1\Q0=PPQ0<,1PS1WQ1\Q1\Q0@1kOI#O1kPI#OQ0IQ0=Q1YPPQ1WPOC:4093N409D|D|eQ01$0GQ0ZQ0ZQ0[Q0[Q00g02jZQ0=,2XQ0VP=P7P;CoQ0TAHE:e9PE4P;PZP5D{%B0S1A%D0S1;'1RIQ0=Q1\Q1AC:RRXLEAPE=75dEAZE0=%B9R>%D9S1O'1RS%zdR{g00mMS11=L{>408[^LEP1P1P9P0H0dR{=ZEd%B;S1B%D;S0Y'1S0}P51159S19Q1BC:S05[^Q1^N1,0RQ0VPePdPZQ1AQ1;J0c'XX3E=dEeQ0?Q0d9HEZ9PEdQ0ePfQ01AyOPd;HAPeQ0bFpPLPePOPPQ0\PdJ0XQ0b#z%ze'tP8PLPMQ0UQ0eP@PCQ0cFmQ0b=66NQ0VQ0ePAPeCoP=PLPMQ0UQ0fP@PCQ0e,42FmA66fNPLPMQ0UQ0hP@PCQ0gFmS0gQ0e=66NP6PNQ0TPEQ0h$00S0cPEP0PhI05Q0ePgPfD{PIP?PBQ1AC:S0\XLERIQ0i=PE95dEAZE0;%zcRRQ11=LR>608S[^LEQ0\AZE{4Q05[^Q1^N1'0Q0]'XX3E=dEhQ0?PE&00cS1`PEP:Q0kI05Q0lPbQ01Ay\Cc;HWPhQ0jFpPLPMQ0UPhP@PC142cFm]V]^]]]T]UXX6Q0TQ0fQ0j9HEN5PEPfQ0iPAD{Q0c=HEN9dEIAZE0NRR%zTS0cQ0cQ11;L>608S[^LEQ0\AZE{NR{Q05[^Q1^N1'0Q0]'XX3ES0\Q0j5dEQ0?Q0l9HEN9PETPbPWQ01Ay\CT;HhQ0jPcFpP6PEQ1`PEPNQ0kI05Q0TP0PgPWQ0iD{Xj6P:Q1`=HENQ0k5HES05PEQ1`PNQ0kH0aJ0=Q0TQ05Q0iPhQ0hD{P6PEQ0j$00S05PEPNPYI05Q0?P0PYQ0kQ01Ay\ChQ0l3HPbPWFpXj6P9Q05=HEN=HEYS1`PEQ05PNPYH0aJ0=Q0?Q1`Q0kQ0lQ01Q0j9y\C;HbPWPhFpPLPMQ0UQ0?Q0mPYQ0kQ0lPbPWP@PCP?PBP2PhQ0jp,5HceilS0UQ0ip,4HerrQ07Q1NQ09Q0>Q0BQ0G#IR2+0TR@,2BS0G%3?S01'0RM'0RL'0R\'0P]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}Q1KPDQ1ICAQ1<Q1=bFbGbHX11X21X4QQ1MQ1[[^11^21^4QQ1Vb>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ1NP\P]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q17Q18P}Q0uPDQ1ECAQ1<Q1=bFbGbHX11X21X4QXIQQ1XQ1?=L95[^11^21^4Q^IQQ1Ub>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ09PLQ1TQ0>PMQ1SQ0GQ01P]PHPGP[P_PVQ0B00W2S01Q0z%32173@[[S0zQ0{Q0|Q0B@0V29UWWS0GQ0{Q0|%3@[]WS0{PaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q1@Q18P}P}Q1_P}Q1JP}Q1HP}Q1GP}Q1]P}Q0B#_R2Q0D$0?60`1S0D9G}~Q1>DJDJDJPDQ0W:0`12S0W9G}~CAQ1<Q1=bFbGbHX11X4QXIQXJQXKQXMQXOQP9P5P;P:Q0E,20=N74Dg129@[^11^4Q^IQ^JQ^KQ^MQ^OQP0Q1QQ0AQ0>Q09Q1NQ07PBQ06O8b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBb`bfP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q1@Q18P}Q0`PDQ1CCAQ1<Q1=bFbGbHX11X4QXIQXJQXKQXMQXOQXRQQ0XQ1D[^11^4Q^IQ^JQ^KQ^MQ^OQ^RQQ1Pb>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBCqFaFaQ07Q08;N\eQ1ZAPEWN9ZE0Q0?Q0Tp,3WFBS1Zp,8Herr_imgAPEbNS1PQ0nQ0jQ0kPcP;P9P0N<1FQ0?$1ER\,2SQ0;#IRQ,1\R2/2>P>Q1OQ0@Q0H#C$01#}#}#IS0H'sR375SH1DP8%B5RM%D5S0k'1S0nP\P2PMC:Q0kQ0n;53,eMQ1BQ0YP?1sB?RLCQQ0}P\P2Q1BC:Q1BQ0YQ0};5@'e3NP0%B:S0Y%D:S0X'1S0`P\P2Q0YC:%B7S06%D7S1NQ06Q1N'1S1N;53'eP8%B4S1Q#3%D4S1>Q1QQ1>'1S0B;53%B=S1]%D=S1GP?PLCQS1HQ1]Q1G'1S1JP\P2Q1]C:Q1]Q1GQ1J;5@'e3NP0%BZ#3%DXS1]%BXS1JQ1]'1S1G;53P8%DdS1_#3%BdS0|Q1_;L3Q0b#BS1SQ0b#DS0bP?PLCQQ1SQ0b'1S1TP\P2Q1SC:Q1SQ0bQ1T;5@'e3NP0%De#3%BAS1S%DAS1T;L3Q0s=PENR39dEIQ0r=PENRA9ZE0PIP9O1S0r[^lES0s+1AAdEIAQ0t=PEN9ZE0Q0r[^lE<1@0Y0PB1?EI3PgO2Q0sP0Q0ePfO2Q0e#BRfQ0e#D'1P?PBPfC:Q0d#BRfQ0d#DR3'1RIAL?Lf808?PIP\P2PfC:S0s%3fS0r%33S0t12I@S0b'0S1U'0S1X'0S1?P]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q1^Q167K5%`;S1^7K9Q18P}Q1:,E~RIQ0^#WR25G}RAQ0;#WS0;=G}~5w}PDQ0;>0U12,E2=G}~9w}ACAQ1<Q1=bFbGbHX11X21XP1XS1S0;1109S0^/25S1:?n;0AL95;S1E1s:;,1;;n9[^11^21^P1^S1S0uP0PBP?Q0p#DS17Q0p#BS1VQ0iO5b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ0sQ1XP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q15Q1^7K9Q18P}%_Q,E2=G}~9w}ARAPDPACAQ1<Q1=bFbGbHX11X21XP1Q1:115Q;n0Q1E11;Q;n9[^11^21^P1P0P\Q17Q1VQ0mO4b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ0rQ1UP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P|Q14Q1@Q18P}Q1CPDQ1CCAQ1<Q1=bFbGbHX11R\Q0xQ1D[^11RQP0Q1VPbO2b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBQ0tQ0bP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1P\PQP0Q17PcO2b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBP]PHPGP[P_PVQ01Q0zQ0GQ0{PaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1Q13Q10Q0yQ12#]Q0w#]Q0:'V'V'V'VQ0v+0L<0;|Q14Q16Q1LQ167K;7K5Q16Q1RQ167K:7K47K9Q18P}P}PIQ0_Q0H#_60U1R|PDP}P}Q0aQ0DPDP}P}Q0CQ1F'EQ0aPDP}P}Q04Q0CPDP}P}P|Q04PDQ0W9G}IE[E[E[E[E[Q1<Q1=bFbGbHX11X21XP1XS1XY1XZ1Q0^Q0H,s5'2Q0E,27Q0<=L=4124ZQ0H,s4/2=AL74@[[[[[^11^21^P1^S1^Y1^Z1P0PCPBP?Q0@Q0q#DQ0q#BQ0jf~p+01Gp+01KQ0UO;b>bEbDb=b<b;b:b9b3bCb8b7b6b5b0b?b@bAbBb`bfFaFaPfP3P?PLCQQ1?'0ebsbTWqWpP9P0O2n2001000000121000000W0WoP9P0O2n2001000000121000000W0WnP9P0O2n2001000000121000000b0WcXLEQ0?Q0TQ1ZAPEhNQ0mPTPbPgP9N91>Q1P9ZE9Q0l=PEN9ZE9Q1B/tM$04Q0?Q0TQ1ZAPEYNQ0pPbQ0oPWP4P:P;P5P9P0N>1=Y08Y05Y04Z0LEZ0KEPEQ0\Q1AQ1;P?PLCQPMQ0kP>Q1OCQ\R^LE'0X3EQ0\P0O1Q0312S?12B>Q0`P5Q19Q0YC:\{^Q1^N140]Q0]PMQ0kP?PLCQQ0YQ0XP>Q1OCQ\R^LE'0P0Q0n/2?12BMQ1NP5Q19Q06C:\{^Q1^N140]P8Q0}P?PBQ1BC:Q0BP5Q19Q1QC:\{^Q1^N1Q0YQ0XP?PLCQQ1QQ1>P>Q1OCQ\R^LE'0RLP0Q1NP?PBQ06C:Q1GP5Q19Q1JC:\{^Q1^N1Q1HQ1JQ1]P>Q1OCQ\R^LEP]PHPGP[P_PVPaP`P^PiPjPFPkPlPmPnPoPpPUP1PKP1PqPsPtP<PuPvPwPxPyPzPrP1PJP1Q0;Q0uP0PBP?%Db%BbPgO5b>bkbDb=b<b;b:b9bEbCb8b7b6b5b0b?b@bAbBQ1HeQ02P1P1Q0|Q1_P>Q1OCQ\RP0P4P5P9P0O3Q1SQ1TP1P1P5P9H0dRR#B%DRCQeXc{XQ1XN1P9P0O2n200110Q00012010V10VXLECqY03Y06P9P0O2n2001000000121000000W0P0O1Q0]Q0]PLP0n010000000W0P0O1n200100000021100010000W0X3EQ0lP;J1<P0PZPeNM19bVbUWVW^W]WTWUQ0eP0PdPXPZP=P4N;18Q0geP0CqQ0VQ0hQ0dQ0eCoeWrY0=P9P0O2n2001000000121000000Y01Y02WVW^W]WTWUWbY09Y0?Y0MXX6Y0UWaY0;W_Y0@Z0S1Z0T1Z0:6Q0ZQ0[Q0VP:P;P5CoQ0VP7P:P;P5P9J0cQ0]Q0~Af=:;B157:;Q0IP:11:;R7Q0EQ0=P:P7Q1\Q11,7;P7POQ1YP:C:P7PPQ1WP:C:3ND|D|'X3NP0n010000000W0WbZ0O1Z0Q1XX6WaW_N911Y00W~P9P0O2n2001000000121000000W0W}P9P0O2n2001000000121000000W0W|P9P0O2n2001000000121000000W0W{P9P0O2n2001000000121000000W0WzP9P0O2n2001000000121000000W0WyP9P0O2n2001000000121000000W0WuP9P0O2n2001000000121000000W0WtP9P0O2n2001000000121000000c0Jo"). Qed.

Abbreviation VO := (PQM.vec_owner segs A PMSP.T3 PMSP.T4 vp op ois lo hi s).
Theorem vec_owner_ok : PQV8.vowner_ok segs A L HI VO.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpOwner ()) ["Owners"] "p'0h01Hh14__x1h24__x2h31rh42H0h53H10h63H11h73H12h83H13h93H14h:3H15h;3H16h<3H17h=7__arithh>7__sat10h?7__sat11h@7__sat12hA7__sat13hB1qhC2q0hD2r0hE4__p1hF4__ffhG8__varmaphH5__withI4__p2hJ4__p3hK4__p4hL4__p5hM4__p6hN4__x3hO4__x4hP1bhQ1BhR4__p7hS4__x5hT4__x6hU1mhV3H18hW3H19hX2HahY7__sat14hZ4__x7h[4__x8h\4__x9h]1xh^2_Hh_2r1h`3H20ha3H21hb3H22hc3HAfhd3Hinhe1Mhf2OBhg3_H0hh4__p8hi4__p9hj7__sat15hk1ghl1lhm2q1hn3srcho2B'hp2BBhq3BB'hr1Dhs2E1ht2E2hu2E3hv2E4hw3EOBhx2Fbhy2H1hz2H2h{2H3h|2H4h}2H5h~2H6i002H7i012H8i022H9i033HBci043HCxi052HHi063HH'i072HPi083HQCi094HSRCi0:3HVWi0;2Hbi0<2Hfi0=2Hii0>4HinXi0?3Hspi0@3LBXi0A2M'i0B2NIi0C2PAi0D3SRCi0E4V8OKi0F5V8OK'i0G2VMi0H2Wxi0I3_H1i0J3_H2i0K3_H3i0L3_H4i0M3_H5i0N3_H6i0O3_H7i0P3_H8i0Q3_H9i0R1ai0S2cri0T2g'i0U1ii0V5lemmai0W2m'i0X3scri0Y2spi0Z4src'i0[2x'i0\1zi0]1pp%0p%1p%2p&0p&1p;2p;1p;:p;5p;6p;4p;3p;7p;<p;Sp;8p;9p-1R0p10000p4p710p9P0g000\R1p4p710R2p8P0p10013R3p4p710p8P0P3p4p7210p8P0g001OR3p4p710R4p8P0g0020R5p4p710p8P0P5p4p7210p8g002MS00p4p70p1003Jp4p7210p8g02UmR0p4p710R6g004ER7p4p710R8p8p1004ap6067111111004p1005^p4p771111110p8g006cS01p4p70R9P2p8P9P8p8P9P6p8P9P4p8P9g007_R4p4p710p8P9g00?6R9p4p710p8p1008Yp4p7210P8p8g00A9j22Tg00B2j1DTg00BWj1ZTg00C<j1KTg00AUj21Tg00S^k114Tg00CZk20\Tg02MYj2`Tg00D7R8j20Tg01m3m:1RTg02kQk51PTg00Nek10PTg01K`k10kTg01LCk11HTg00DRS02k21ATg0096k10MTg01n6j6xTg01o2j43Tg0207j2YTg01kmk113Tg00=_j3HTg02lSk112Tg02mOk111Tg02nLk10~Tg021ok40XTg023jj18Tg024jj16Tg025jj17Tg022lj3}Tg02[DR6j3lTg026kj4hTg027gj4iTg01Amk10;Tg00G3j2?Tg00GOk20^Tg00H7k30]Tg02N9k20:Tg02Njk209Tg00;kk10KTg02OKk208Tg01?Uj2tTg02Ohk207Tg02POk206Tg02Q6k204Tg02Q\k203Tg00>9k10[Tg00K8k110Tg00L4k10}Tg00LRk10|Tg00M`k20YTg00Ofk20{Tg00PHk20zTg00Pbk20yTg00QNk30xTg00Qmk40wTg01Lek20WTg00NCk10VTg00M=k20UTP7k60ITg00T]j2nTg00ZUk10vTg00OCk30TTg02\@k10uTg02\^k20tTg00H[j1UTg02]?k30STg00I:k20sTg00JLk20rTg02]hk20pTg00=?k30CTg00^mk61QTg01ITk30RTg00X@k30QTg02oHk11OTg030Dk11NTg00nJj1cTg01A0j1dTP4j3VTg02`Lk50ATP3k30@TP1j3FTg00jmk10OTg00oIk21JTg01QWk71ITP0k40jTg00Xck400Tg00YXk30iTg00h3k50hTg02cDm<1GTg00hQj4TTg00?Xk21FTg00@1k31ETP9k31DTg011Hk61CTg031@mS1@Tg032Ik81?Tg01PSm91>Tg0213k60?Tg028dk50=Tg01X1k70>Tg00:Tj2uTg01=Yk11=Tg01>Wk11<Tg02;bk11;Tg02DWk81:Tg01@2k10dTg02=ek50LTg029ek10ZTg00KVk219Tg00[Tk418Tg00Z2k31BTg00\2j4{Tg00\]j7sTg00]Ak70JTg00]ej8vTg00^Ik617Tg00Ick316Tg00ilk71KTP5k315Tg00jPk31LTg00kjk41MTf2R5f1R9'1f0R0'2p=E%D0#D#D#Dp=y%D0#Dp>02g00<DR1g00_QR37H0p=If6R4f5R7P6g02i^R2f4R:f3R;P5P9P0N91>p>0<P7P6P2P:P;P5J0?1Y90'0p=Mf7R<P4P6P7P:I0=A};59/00'0p=LP4P6P7P:P;P5P9K0>/00p=J12351290'0p=4AH143AH17:'uAH1;3AH159'u/00'0p=9P4P6P2P7P:&1=;&1<5&1;9L1:/00p=:P:P6P2P;P5&0d9J0?/00p=;P:P6P;P5&0;9I0L/00p=>P4P7P:g02EXR=CiAl;59/00'0p=AP4P6P7P:P;P5&0Z9K0>/00p=GP<P4P7P3CiP:P;P6P5P9I0=/00'0p=SP<P4P7P:CiP;P5P9P3Ch/00'0p=_P:P;P5P9Ch/00p=QAl;59/00p>0BA};59/00p>0mP:P;P6P5P9I0=/00p>01P4P7P:P3ChP;P5P9P3Ci/00'0p>0gP5P9P0P3Chp>0fP5P9P0P3Cip>0eP;P5P6P9P0I0=p>0NP7P6P:P;P5P9&0Z0K0>p>0cP5P9P0P=Cip>0bAl<47P:P6P;P5P9I0L/00'0p>0aP;P6P5P9&0;0I0Lp>0`P;P6P2P5P9&0d0J0?p>0qP7P6P:P;P5P9P0K0>p>0lP;P6P2P5P9P0J0?p>0_1230p=511909H15p=b1290,05p>05AH190p=p21910p=aP1P5P9P0H18p=P20U10p=^20Y10p=[B1B190p=<P5g00_oS03g00`NR>P>g00`nS04P1P9g01K9R?P0C{g00b5R@Fsp>0H1239/00p=WP1P9g00bUP0C{p=~P5Q03P>P>Q04P1P9g00aNRAP0C{P@Fsp=@P9Q03P>P>Q04P0P@Fsp>0FP5Q03P>P>Q04P9P0K0Jp=oP;Q03P>P>Q04P5P9P0Gvp==P:Q03P>P>Q04P;Q03P>P>Q04P5P@FsP9P0Gvp>0EP4P7P:P;P5P9P0H00H00p=R12;51290'up=NP9Q03P>P>Q04P0J17p=eP1P9PAP0C{p>0DP:Q03P>P>Q04P;P5P9Q03P>P>Q04P0P@FsGvp=mP:Q03P>P>Q04P;P5Q03P>P>Q04P9P0K0JK0Jp=O1090,05p=]1090,05,0;,0:p=g20s10p=fB16190p=XP1P9P?P0C{p=zP7Q03P>P>Q04P:Q03P>P>Q04P1P;PAP5C{P@FsP9P0Gvp=\P4Q03P>P>Q04P7P:P;Q03P>P>Q04P5P9P0GvGvp=|1259/00p>0oP5Q03P>P>Q04P9P0K1Kp=q1290,u5p=r1259/u0p>0n12;5/u9/00p=j12:;1259/00'0p=wAV5909V:;p=kB15110p=BB1L110p=CP1P1P9P0H1Mp>0Gp,4HlayS05p,2loR@p,2opRA'2S06g00c<R?p,2hiRB5EAS07p,3oisRC,2@S08g00d;S09#DRD#DS0:#DRE#Z#y#KS0;,1CS0</2BS0=p,1LS0>$14S0?,2BS0@%KDS0A%ZDRF#ZS0B#Z#ZS0C#KRG+0\S0D,2BS0E%DERH$02S0F$02#yS0G#KS0H/2@S0I%KERI,`ARJ#IS0J1`CIRK#IS0K'0S0L'0S0M'0S0N'0S0O'0S0P'0S0Q'0S0R'0P8Q06Q0Rp,4segsRLp,1ARMQ0>p,2HIS0SPLPMP6P2p,2vpS0TPAPCP@PBp,1sR2N:1RS0UI1PR6P0Q06Q0RP8Q07Q0QP6P0Q07Q0QP8Q08Q0PP6P0Q08Q0PP8Q0=Q0OP6P0Q0=Q0OP8Q0@Q0NP6P0Q0@Q0NP8Q0EQ0MP6P0Q0EQ0MP8Q0IQ0LP6P0Q0IQ0LP8Q0JQ0KP6P0Q0JQ0KPLPMQ0>Q0SQ0UQ0F$0PS0V$0k&0PE$0kS0W$1HS0X[S0Yg01_US0Zg01aRS0[21A11RE$0MR6Q0UP:P;P5P9P0ExP8PLPMQ0TP7PAPCP2P:P;P5C3K0<1Y;5&132S0\9H69'0PLP4Q0U$12S0]Q0U$11S0^Q0^%KHRH'1S0_P7PLPMP4Q0]/1IS0`P4Q0]Q0:#ZS0a#D#Z#D$02#KRNPLP4Q0U$0~S0bP:P:P;EMGLFJP0PLPMQ0TP<PAPCP2P4P7P:C3K0<1Y47Q0\9H6:'0P81Y<4Q0\9H67PLf:S0cQ0]Q0^Q0_f9ROPLPMQ0cQ0`Q0cQ0]PNPLQ0cQ0bf8RPPPP<EMGLFJP01YOPQ0\9H6PP8PLf=RQPAQ0TH0XPQPAP?PQPAQ09#ZS0d#DS0e#DS0f#D#KRRPLPQ11AIRSP2f<S0gf;S0hQ0cC3RT#8RUPLPQQ0a#K,1ARV%6TRWPLPQQ0f#K,1ARX%7TRYPLPQ11AHRZPLPQ%DFS0i#D#K,1ARFPLPMPQg010G,1AR[/1IR\PLPQP[PC11CHRHPTPLPQg01dT,1AR]PQP]PIPLPQg01eV,1AR^PTPLPQg01fV,1AR_PTPLPQg01gV,1AR`PTPTPTPUPUQ09#KRUPWPWPU11=UR=94YYF9F:D;D>FAFGGSG_DQDQH0BH0mPLf>S0jP[PCPHPQPLPMQ0jP\Q0jP[PNPLQ0jP_Q0gQ0gQ0hEMGLFJP7PLf?S0kPAQ0TH0Xf@RYPAP?PYPAPRPLPYPSP2Q0kQ0jPQC3RW#8RTPLPYPV%6WRaPLPYPX%7WRbPLPYPZPLPYPFPLPMPYP\PLPYP[PCPHPWPLPYP]PYP]PIPLPYP^PWPLPYP_PWPLPYP`PWPWPWPTPTPUPaPaPUA4bb=F9F:D;D>FAFGGSG_DQDQH0BH0mP8fARb?}A?PbPAPRPLPbPSP2PYQ0kQ0jC3Ra#8RTPLPbPV%6aRWPLPbPX%7aRcPLPbPZPLPbPFPLPMPbP\PLPbP[PCPHPaPLPbP]PbP]PIPLPbP^PaPLPbP_PaPLPbP`PaPaPaPTPTPUPWPWPUA4cc=F9F:D;D>FAFGGSG_DQDQH0BPLfBS0lP[PCPHPbPLPMQ0lP\Q0lP[PNPLQ0lP_PYPYQ0kEMGLFJP0fCS0m?}A?fDR?PAPRPLP?PSP2Q0mQ0lPbC3Rc#8RWPLP?PV%6cRTPLP?PX%7cRaPLP?PZPLP?PFPLPMP?P\PLP?P[PCPHPcPLP?P]P?P]PIPLP?P^PcPLP?P_PcPLP?P`PcPcPcPWPWPUPTPTPUA4aa=F9F:D;D>FAFGGSG_DQDQH0BP8fERa?lARPLPaPSP2P?Q0mQ0lC3RT#8RWPLPaPV%6TRcPLPaPX%7TRdPLPaPZPLPaPFPLPMPaP\PLPaP[PCPHPTPLPaP]PaP]PIPLPaP^PTPLPaP_PTPLPaP`PTPTPTPWPWPUPcPcPUA4dd=F9F:D;D>FAFGGSG_DQDQPLfFRdP[PCPHPaPLPMPdP\PdP[PNPLPdP_P?P?Q0mEMGLFJP0fGS0n?lARPLfHRcPSP2Q0nPdPaC3RW#8RTPLPcPV%6WRePLPcPX%7WRfPLPcPZPLPcPFPLPMPcP\PLPcP[PCPHPWPLPcP]PcP]PIPLPcP^PWPLPcP_PWPLPcP`PWPWPWPTPTPUPePePUA4ff=F9F:D;D>FAFGGSG_DQDQP8PLfIS0oPSP2PcQ0nPdC3Rf#8ReChPLQ0oPV%6fRTPLQ0oPX%7fRWPLQ0oPZPLQ0oPFPLPMQ0oP\PLQ0oP[PCPHPfPLQ0oP]Q0oP]PIPLQ0oP^PfPLQ0oP_PfPLQ0oP`PfPfPfPePePUPTPTPUA4WW=F9F:D;D>FAFGGSG_DQPLfJS0pP[PCPHQ0oPLPMQ0pP\Q0pP[PNPLQ0pP_PcPcQ0nEMGLFJP0PLfKS0qPSP2Q0pQ0oPcC3#8ChPLfLS0rPVP2Q0qQ0pQ0oC3RS#6RWPLQ0rPX%7SRTPLQ0rPZPLQ0rPFPLPMQ0rP\PLQ0rP[PCPHPSPLQ0rP]Q0rP]PIPLQ0rP^PSPLQ0rP_PSPLQ0rP`PSPSPS%8SRSPSPUPWPWPUA4TT=F9F:D;D>FAFGGSG_DQP8PLfMS0sPVP2Q0rQ0qQ0pC3RT#6RWChPLQ0sPX%7TRSPLQ0sPZPLQ0sPFPLPMQ0sP\PLQ0sP[PCPHPTPLQ0sP]Q0sP]PIPLQ0sP^PTPLQ0sP_PTPLQ0sP`PTPTPT%8TRTPTPUPWPWPUA4SS=F9F:D;D>FAFGGSG_PLfNS0tP[PCPHQ0sPLPMQ0tP\Q0tP[PNPLQ0tP_Q0rQ0rQ0qEMGLFJP0PLfOS0uPVP2Q0tQ0sQ0rC3#6ChPLfPS0vPXP2Q0uQ0tQ0sC3RV#7RSPLQ0vPZPLQ0vPFPLPMQ0vP\PLQ0vP[PCPHPVPLQ0vP]Q0vP]PIPLQ0vP^PVPLQ0vP_PVPLQ0vP`PVPVPV%8VRWPWPU%6VRVPVPUA4SS=F9F:D;D>FAFGGSG_P8PLfQS0wPXP2Q0vQ0uQ0tC3RS#7RVCiPLQ0wPZPLQ0wPFPLPMQ0wP\PLQ0wP[PCPHPSPLQ0wP]Q0wP]PIPLQ0wP^PSPLQ0wP_PSPLQ0wP`PSPSPS%8SRWPWPU%6SRSPSPUA4VV=F9F:D;D>FAFGI01K0gPLfRS0xP[PCPHQ0wPLPMQ0xP\Q0xP[PNPLQ0xP_Q0vQ0vQ0uEMGLFJP0PLfSS0yPXP2Q0xQ0wQ0vC3#7CiPLfTS0zPZPLQ0zPFPLPMQ0zP\PLQ0zP[PCPHP2Q0yQ0xQ0wC3RXPLQ0zP]Q0zP]PIPLQ0zP^PXPLQ0zP_PXPLQ0zP`PXPXPX%8XRVPVPU%6XRVPVPU%7XRX?4X=F9F:D;D>FAFGI01K0gP8fURX>0fLZPLPXPFPLPMPXP\PLPXP[PCPHP2Q0zQ0yQ0xC3RVPLPXP]PXP]PIPLPXP^PVPLPXP_PVPLPXP`PVPVPV%8VRSPSPU%6VRSPSPU%7VRV?4V=F9F:D;D>FAFGGSPLfVS0{P[PCPHPXPLPMQ0{P\Q0{P[PNPLQ0{P_Q0zQ0zQ0yEMGLFJP0fWS0|>0fLZPLfXS0}PFPLPMQ0}P\PLQ0}P[PCPHP2Q0|Q0{PXC3RXPLQ0}P]Q0}P]PIPLQ0}P^PXPLQ0}P_PXPLQ0}P`PXPXPX%8XRZPZPU%6XRZPZPU%7XRX?4X=F9F:D;D>FAFGGSP8fYS0~>0eLFPLPMQ0~P\PLQ0~P[PCPHP2Q0}Q0|Q0{C3RXPLQ0~P]Q0~P]PIPLQ0~P^PXPLQ0~P_PXPLQ0~P`PXPXPX%8XRZPZPU%6XRZPZPU%7XRX?4X=F9F:D;D>FAFGI01PLfZRXP[PCPHQ0~PLPMPXP\PXP[PNPLPXP_Q0}Q0}Q0|EMGLFJP0f[S10>0eLFPLPMf\S11P\PLQ11P[PCPHP2Q10PXQ0~C3RFPLQ11P]Q11P]PIPLQ11P^PFPLQ11P_PFPLQ11P`PFPFPF%8FRZPZPU%6FRZPZPU%7FRF?4F=F9F:D;D>FAFGI01P8PLPMf]S12P\H0NPLQ12P[PCPHP2Q11Q10PXC3RXPLQ12P]Q12P]PIPLQ12P^PXPLQ12P_PXPLQ12P`PXPXPX%8XRFPFPU%6XRFPFPU%7XRX?4X=F9F:D;D>FAFGPLf^S13P[PCPHQ12PLPMQ13P\Q13P[PNPLQ13P_Q11Q11Q10EMGLFJP0PLPMf_S14P\H0NPLf`S15P[PCPHP2Q14Q13Q12C3RXPLQ15P]Q15P]PIPLQ15P^PXPLQ15P_PXPLQ15P`PXPXPX%8XRFPFPU%6XRFPFPU%7XRX?4X=F9F:D;D>FAFGP8PLfaRXP[PCPHP2Q15Q14Q13C3RFJ0cPLPXP]PXP]PIPLPXP^PFPLPXP_PFPLPXP`PFPFPF%8FRZPZPU%6FRZPZPU%7FRF?4F=F9F:D;D>FAPLfbRFP[PCPHPXPLPMPFP\PFP[PNPLPFP_Q15Q15Q14EMGLFJP0PLfcRZP[PCPHP2PFPXQ15C3J0cPLfdRVP]PVP]PIPLPVP^P2PZPFPXC3RXPLPVP_PXPLPVP`PXPXPX%8XRSPSPU%6XRSPSPU%7XRX?4X=F9F:D;D>FAP8feRX>0bL]PXP]PIPLPXP^P2PVPZPFC3RF$0;PLPXP_PFPLPXP`PFPFPF%8FRSPSPU%6FRSPSPU%7FRF?4F=F9F:D;L0aPLffRFP[PCPHPXPLPMPFP\PFP[PNPLPFP_PVPVPZEMGLFJP0fgRZ>0bL]fhS16P]PIPLQ16P^P2PZPFPXC3RX$0;PLQ16P_PXPLQ16P`PXPXPX%8XRSPSPU%6XRSPSPU%7XRX?4X=F9F:D;L0aP8fiRX?l]IPLPXP^P2Q16PZPFC3RFPLPXP_PFPLPXP`PFPFPF%8FRSPSPU%6FRSPSPU%7FRF?4F=F9F:D;D>PLfjRFP[PCPHPXPLPMPFP\PFP[PNPLPFP_Q16Q16PZEMGLFJP0fkRZ?l]IPLflR]P^P2PZPFPXC3RSPLP]P_PSPLP]P`PSPSPS%8SRWPWPU%6SRWPWPU%7SRS?4S=F9F:D;D>P8PLfmRSP^P2P]PZPFC3RFH0`PLPSP_PFPLPSP`PFPFPF%8FRWPWPU%6FRWPWPU%7FRF?4F=F9F:D;PLfnRFP[PCPHPSPLPMPFP\PFP[PNPLPFP_P]P]PZEMGLFJP0PLfoRZP^P2PFPSP]C3H0`PLfpR]P_P2PZPFPSC3RSPLP]P`PSPSPS%8SR^P^PU%6SR^P^PU%7SRS?4S=F9F:D;P8PLfqRSP_P2P]PZPFC3RFH0qPLPSP`PFPFPF%8FR^P^PU%6FR^P^PU%7FRF?4F=F9F:PLfrRFP[PCPHPSPLPMPFP\PFP[PNPLPFP_P]P]PZEMGLFJP0PLfsRZP_P2PFPSP]C3H0qPLftR]P`P2PZPFPSC3RSPSPS%8SR`P`PU%6SR`P`PU%7SRS?4S=F9F:PLfuRSP[PCPHP]J0lPLPMPSP\H0NR\A}S[NS17PLPSP_PZH0_S181YZFS19'0RZ'0RF'0PbP\PFPaQ17PZ%50S1:1?0NS1;'0Q0A00^GRZQ0A,?3S1<%5GQ0D,?3[[RFQ0A#5S1=g00d`S1>Q0A@0]G9UWXRGQ1=Q1>Q0D#5[]XR\20:AIRS%5A%5IS1?%5JR][[RH20:CIR=%5CQ1?%5KRU[[R`209CIR^%IIS1@$0KS1A208CIRW,tI=bCK[RT207CIRe1?3IS1B1?KI,0U[RU206CIRf1?I3S1C1?IK@05K3[Rg204CIRhQ1@%IW[Ri203CIRjQ1@1pKC[RkPWP1PKP1209AIRlQ1A208AIRm,tI=bAJ[Rn207AIRoQ1B1?JI,0][R]206AIRpQ1C1?IJ@05J3[Rq204AIRrQ1@%Im[Rs203AIRtQ1@1pJA[RuPmP1PJP1P8Q0m#5Q0m/?N11R?,1A11ARRv;b?Q0l%5a1?dNg00e<S1D$0[RwQ1D$0MRx%a5S1E&101S1F7P9S1G&0}1Ry&0|1RzQ09-0Y1R{%^RS1H%[DRD'<'<Q1H,<{S1I/<D40HQ04-0{zR|P0P5g00g3R}g00gSR~+0z20y05=H}~dB0x139H0wR~bFbGbHX11X2111R9R},10110RS1J;b9^11^21P0PcPAO2b=WWWVP9P0O2n2001000000120000000bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bA11A}?bv9P111R5R},1AQ0XfyQ0V00W0O1Q0W$0VS0W3H$0KZ0\1PVP}PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1P8%5?1??N11RaRVQ0f#Z#y#KS1K,?V'WQ0m%5dQ0n/?NPwPx%a9S1LPyPzPz%^NS1M,~{&0V>RVPz20U13S1N=@z{S1OPVQ1NQ1H/<{S1P5@zQ1PQ1K#^S1Q'~-0Fz5ozC=I0EP|P~bFbGbHX11Q1;%59S1PQ1K,?},W}[[^11P0Q0oP9P5O3b=WWWVP9P0O2n2001000000121000000bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAO211v5P0J0Ib0Q0XfwQ0V11[9+0WO1Q0W3H$0KeY0=Z0U1Q17eQ18Q19P9PXFRFRY0QWpP9P0O2n2001000000121000000W0Y0PP9P0O2n2001000000121000000W0Y0OP9P0O2n2001000000121000000W0Y0NP9P0O2n2001000000121000000W0Y0DP9P0O2n2001000000121000000W0Y0BP9P0O2n2001000000121000000W0Y0MP9P0O2n2001000000121000000W0Y0LP9P0O2n2001000000121000000W0Y0KP9P0O2n2001000000121000000W0Y0JP9P0O2n2011000000121000000W0Y0IP9P0O2n2011000000121000000W0WgP9P0O2n2011000000121000000W0WrP9P0O2n2011000000121000000W0W^P9P0O2n2011000000121000000PLPQQ0]Q0^Q0_Q0gPLPMPQQ0`PQQ0]PNPLPQQ0bQ0hQ0hQ0cEMGLFJeW^Y0EP9P0O2n2001000000121000000W0Y0CP9P0O2n2001000000121000000W0WfXk1W]WnWe12@v11vNS0`/2BS19Q08Q0=Q0B#D#y#KS18,1ARX,2@S1711XRR}/2BS0WQ0@Q0E1`vIS0X#IS1;Q0K1`XIS1R#IS1SQ0IQ0`PCQ0<PvCNS1TP}PvQ0`PXCNS0`P}PCQ0<PXCNS1UQ0?Q0G#D$02#y#y#KS0G'nS1V/2@S1WQ0>$0vS1XQ0:#KS1Y'1S1Z/2@S1['0S1\'0S1]'0S1^'0S1_'0S1`'0S1a'0S1b'0S1c'0S1d'0S1e'0S1f'0S1g'0S1h'0S1i'0PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1p-0R}PwPxQ1GPyPzA@z{DS1j1ez:S1k5ozS1lPVPzQ1H,<D-0D{DmP|P~bFbGbHX11X21WE1209S1m/05S1n115R,29[^11^21^E}P0Q1K=EABS1oQ08Q0=Q0@Q0EQ0I%I9S1p%IP'0S1q'0S1r'0S1s'0S1t'0S1u'0S1v'0PAP@Q05O4S1wb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ19Q1iPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzPzQ1kPzQ1Q,<{=@zDS1Q1ez7S1iDOS19PVQ1IQ1M'<S1M=@zDS1xC=P|P~bFbGbHX11X21XE}XI}Q1K=E09S1y=]5;S1z119RS1{?EN5S1|[^11^21^E}^I}P0Q1vQ06PBPAQ05O5S1vb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ08Q1hPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzPzQ1kPzQ1iQ1j1ez4S1h5ozDOPVQ1jC=P|P~bFbGbHX11X21XE}XI}XJ}Q1m/0:9]5;1295S1}[^11^21^E}^I}^J}P0Q1uQ1oQ06PCP@Q05O6b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAS1uQ0=Q1gPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzPzQ1kPzQ1iPzQ1hPzQ0;#^S1g,<{=@zDS1~1ez<S20DODOPVQ1~C=P|P~bFbGbHX11X21XE}XI}XJ}XK}P5P;P:Q0;=E09P7DgQ0;,19S1~/25[^11^21^E}^I}^J}^K}P0Q1tQ08Q1oQ06PBPCQ05O7b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAS1tQ17Q1fPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ1lPVPzQ18#^S1f,<D-0D{DmP|P~bFbGbHX11X21XE}Q1nQ18,15,29[^11^21^E}Q1wb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ0WQ1ePZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ19PVQ1f,<{S1eQ1H'<S0W=@zDS17C=P|P~bFbGbHX11X21XE}XI}Q1zQ18,19S21?ER5S22[^11^21^E}^I}Q1vb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ0@Q1dPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzPzQ1kPzQ1iPzQ1hPzQ20Q1j1ezPS1d5ozDODOPVQ1jC=P|P~bFbGbHX11X21XE}XI}XJ}XK}XL}P5P;P:P7Q1m/04DgQ1}[^11^21^E}^I}^J}^K}^L}P0Q1sQ0=Q08Q1oQ06Q0?PBQ05O8b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ0EQ1cPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyPzPz1ez;S1cPzQ1kPzQ1iPzQ1hPzQ20PzQ0A#^S1sQ0C$0P60T1S0C9@z{S1mQ1dDODODOS23PVQ1mC=P|P~bFbGbHX11XE}XI}XJ}XK}XL}XM}P9P5P;P:Q0D,20=]74DgS1mQ0D,29[^11^E}^I}^J}^K}^L}^M}P0Q1rQ0@Q0=Q08Q1oQ06PBQ05O8S1rb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1;Q1bPZPFPGP\PSPH20:vI%5vQ1?Q0X#5S1b[[P=P`209vIQ1A208vIS1;,tIQ0X5bv[207vIQ1BQ1bQ0X/?I'0[206vIQ1CQ0X,?IQ0X<053[204vIQ1@Q1;#I[203vIQ1@Q0X/pv[Q1;P1Q0XP1P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1Q1DQ09$0u-0t1Rvg00ehS09#US0X#US1;#US1b#US24#US25#U#US26#US27#U#U#US28#f60S1Q27#fS27Q26#fQ24#fS24:0S1v'X'X'XQ28#U#fQ27:0S1vQ25#fS25Q0X#fRv'X'X'XQ09-0s1,XvS09g00fGS0X+0r+0p+0pRvQ1D@0Cvw40CS27PxQ1F%a<7PO%a7S28%aO7P57PO%a:S26%aP7PO%a4S29Q1F7P;7PO7P9S2:PyPzPzPzQ03P>P>Q04%^IR>Q1N60HzJ1QS04PVPzQ0d#ZS03#[RvQ03#D#[:0R1>Q0i#[S0i'<'zDmS03PVPzPzQ04PVPzQ0a#[S0aQ0e#Z#[:0R1>Q0B#[S0B'<'zDmS2;PVPzPzQ1N/~>-0FzS2<PVQ1O1~{>-0Fz5ozC=S2=PVPzPzQ04PVPzQ1H,<vS1HQ0f#[:0R1>/<{S0f'zDmPVPzPzPzQ1NQ1HPVPzPzQ1NP>PVQ1OE\S1HE\PVPzPzQ0BQ1N'zPVPzPzQ0iQ1N'zPVPzPzQ0H#^S2>Q0e#[S0ePVPzPzQ0eQ0aPVPzPzQ0ePvPVQ1N:0Hz{S0aE\E\E\I0EI0ES2?C=F|F|P|P~bFbGbHX11X21XN1XO1XS1XT1XZ1X[1X\1Q1@g00>Y[R>1tIOS2@=b;7[S2AQ2@=b7<\>S2@Q1B1?;I,W;[S2B114RS2CQ0c,tI/1:S2D'p\>Q2C#5Q1?%54[S2C[Q0c#IS2EQ2EQ0H/2PQ0h,2OQ0cQ0h'2Q2E[[[[[S2E[[[[[^11^21^N1^O1^S1^T1^Z1^[1^\1P0P5POPYPPP9PCPAP@Q0kP<Q0jP?PaQ0nQ0qQ0rQ0vQ15Q16OCS16b=b_bmbbbab`bWbVbDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAbYQ0KQ1aPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyPzPzQ2<PVQ1OQ1c5ozC=PVPzPzQ1kPzQ1iPzQ1hPzQ20PzQ1dPz1ezOS2<PzQ0c,ezPzQ0h,ezQ0aDODODODOPVQ0aF|P|P~bFbGbHX11XE}XI}XJ}XK}XL}XM}XR}Xh}Xi}Q1BQ1P/05[P;P:P7P4P<PPPOQ0cQ1pDgDg%I5[[^11^E}^I}^J}^K}^L}^M}^R}^h}^i}P0Q1pQ0IQ0EQ0@Q0=Q08Q1oQ061?PIPPPQQ05O<b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1SQ1`PZPFPGP\PSPH20:XI%5XQ1?Q1R#5S1`[[P=P`209XIQ1A208XIS1?,tIQ1R5bX[207XIQ1BQ1`Q1R/?I'0[206XIQ1CQ1R,?IQ1R<053[204XIQ1@Q1?#I[203XIQ1@Q1R/pX[Q1?P1Q1RP1P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1Q27PxQ2:PyPzQ03PVPzQ2;PVPzQ2=PVPzPzQ04PVPzQ1f,<vRXQ0f'zDmPVPzPzPzQ1NPXPVQ1HE\PVQ2?C=F|F|P|P~bFbGbHX11X21XN1XO1XS1XT1XZ1X[1X\1Q2AQ2@Q2BQ18,14RXQ2D'p\>%5XQ2C[Q2E[[[[[^11^21^N1^O1^S1^T1^Z1^[1^\1Q16b=b_bmbbbab`bWbVbDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAbYQ0IQ1_PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyPzPzQ1cPzQ1kPzQ1iPzQ1hPzQ20PzQ1dQ2>=@z{RXQ2<5ozDODODOS2<PVPXC=P|P~bFbGbHX11XE}XI}XJ}XK}XL}XM}XR}P9P5P;P:Q0H@0o0<9]74DgS2>Q0H/29[^11^E}^I}^J}^K}^L}^M}^R}P0Q1qQ0EQ0@Q0=Q08Q1oQ06P@Q05O9S05b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1TQ1^PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ1QQ1g,<DRX=@z{5qzS1^PVQ1xQ1I9@zX5qzC=P|P~bFbGbHX11X21Q1yQ1~;r0S1~Q1|Q0;,15S1yQ1{3r[^11^21P0PCPAp,4HdisS1|O3S1{b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ0`Q1]PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyQ0WQ1I5@zQ1MQ1e5@z5qzP|P~bFbGbHX11Q18,10R>/1RQ1JQ1J?EN>40n^11P0PAO1b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1UQ1\PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ1^PVQ17Q1e9@zX5qzC=P|P~bFbGbHX11X21Q1~Q22Q1yQ213r[^11^21Q1{b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1WQ1[PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ0G#^S1[:0Q1{=@zDRXPVPXC=P|P~bFbGbHX11X21Q0G,n0/29Q0G,n9/25[^11^21P0P@Q0?p,5HceilS1WO3b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ1Y#^S1{,<{=@zDRXPVPXC=P|P~bFbGbHX11X21Q1Y=E09Q1Y=E95[^11^21P0P@Q1Xp,4HerrS1~O3b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAFRFRFRFRFRFRFRFRP@P[11[NRXPBQ08Q0=P@P_11_RR>PBQ0@Q0E1`[I#IQ0K1`_I#IQ0IPXPCQ0</2[P>P[12X_P>PCQ0</2_Q1\CjCjCj3]DgDw3]DweQ0U$1OR_Q0]Q0]/1NRNQ0U$1NR>P_Q0^Q0^Q0;'1RXP>P_Q0bQ0b/1RR[P>P>Q0?P>Q0DQ0]/`I#IQ0^/`I#IQ0b/`I#IQ0H/2_PNQ0^Q0],2XP[Q0]Q0b,2NP[Q0^Q0b,2XQ1VQ1Z/2_80o_CjCjCjDgDwDwDwDweQ01$0MQ0YQ0YQ0ZQ0ZQ0[Q0[Q00g02jZ12Q_Q0UQ0hPOP<P7P;ExQ0SPEQ0c#cPE%dPAVE:YDkP;Q0gP5I0A%B0S0H%C0S1\'1S0<P_P>Q0HCNS1yXPEPEQ0h#cPE%dOP7Dk60@EAFE0<%B9R>%C9S22'1S21Q0j$0OR_g00mM=E_>20G90R_Q0j#d5FE%B:RX%C:R['1S17P51159S1ePXCNS1^[`0W1^o1Cj[^PEQ1yQ0c9FE_%B;RN%C;S1U'1RIP5Q1ePNCNS1J[^U1^Q1'0X3E>0@EYQ0>AVEP?Q0mQ0lQ01Q0]Q0^+1JPEQ0b00GR&0[E60CEPbDkPYQ0kK1IPLPYQ0]Q0^Q0_Q0jJ0lQ0k$0O&0OY'pPLQ0lQ0bQ0jH0_Q0k/YQPOQ0UPaQ0mPbQ0kPQExP8PLPMQ0TPdPAPCP2P?Q0lPYC3K0<Q0l/YYQ0jQ0\5H6'0Q0UPdP?Q0lPYQ0kExP0PLPMQ0TPcPAPCP2PdP?Q0lC3K0<Q0m,YaQ0\9H6b'0P81Yd?Q0lQ0\5H6Q0UQ0pPcPdP?Q0mExP01YcdQ0\9H6aP6Q0r#cS0\Q0p#dS0b=VEdRRQ0x5VES0_5VEQ0SP0PdQ0uPaI0AXl6P6PEQ0bPEPdQ0xDkQ0SQ0s#c=VE0PdQ0uPaI0AXl6PbQ0_PEQ0bPdQ0xH0jJ0IQ0\=VERQ0x5VES0bPEQ0\PRQ0xH0jJ0IQ0SQ0bPaQ0tP?I0APLPMQ0TQ0>Q0yQ0nQ0xQ0wQ0vQ0uQ0tPAPCP@PBP2Q1WP?Q1~Q06Q1oQ08Q0=Q0AQ0F#KR2+0\RA,2BS0F%5@RM'0RL'0Ra'0RR'0PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ1lPVQ1jC=P|P~bFbGbHX11X21XE}Q1nQ1}[^11^21^E}Q1wb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1oPRPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1GPyPzQ19PVQ1QC=P|P~bFbGbHX11X21XE}XI}Q1zQ1K=E95[^11^21^E}^I}Q1vb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ08PaQ1uQ0=PLQ1tQ0FPMPZPFPGP\PSPHQ0A00^2S0FQ1<%521?3A[[S1<Q1=Q1>Q0A@0]29UWXS0AQ1=Q1>%5A[]XS1=P=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyPzQ23PVPzQ1sQ0V60T1S1s-0D{DmP|P~bFbGbHX11XE}XI}XJ}XK}XL}XM}Q1m129A[^11^E}^I}^J}^K}^L}^M}Q1rb=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAbYbjPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyPzQ2<PVQ1OC=P|P~bFbGbHX11XE}XI}XJ}XK}XL}XM}XR}Q2>Q1P[^11^E}^I}^J}^K}^L}^M}^R}Q05b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAH00FRFRQ06Q07;]ReQ1|AFE0cPEQ0u#cRRQ0s#dR}Q0o5VER2P9AFE9RAFE92PEP}Q0oP9AFE9}Q0o9FE9<0i0I0h40iI0hAVER29FE9Q0>Q0Sp,3WFBp,8Herr_imgPEQ0v#cPEQ0t#dQ0pDkQ0{Q0oQ0xPcP;P5P0N<1G%B5R2%C5RR'1R}Q1XQ1Z/22Q1V94R},W2CjP8PIQ1XQ1ZPNCNQ1UQ1V74I,WNPXP[P@1nB@R}CTQ17Q1XQ1ZPXCNQ17=4[A,WX3]P0%B7S17%C7S1U'1Q1XQ1ZQ17CN%B4R3%C4RMQ1V9E3M'W'WP8%B<RM#5%C<S0SQ0S,1MS0>Q1V34%BPR3%CPRLP@P}CT113LRaQ1XQ1ZP3CNA4LaA,W33]P0%BO#5Q0c#CROQ0c#BQ1V7EO'WP8Q0h#CS1|#5Q0h#BS05Q1|Q1V3EQ0g#BROQ0g#CRaP@P}CT11OaS0gQ1XQ1ZPOCNQ0g=4aA,WO3]P0%CQ#5Q0j#BQ0j#CQ1V3EQ0<P@PBQ0HCNROXPERaPEQ12#cPEQ10#dQ0|DkS0|60@EPEQ13#cPEQ11#dQ0}DkS0}9FE0PaP9O1S11[^]ES13+1FQ0}:0@EaPEQ14#cPEQ12#dQ0~Dk9FE0Q11[^]E<1E0Y0VQ0|:1DEaQ0wO2Q13P0PYQ0jO2%BYRa%CY'1P@PBPaCN%BbRa%CbS13'1RbAE@}a80n@PbQ1XQ1ZPaCNS1Z%5aS0wQ13#5S0|12bAS11'0S0~'0S12'0S14PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ26Q1F7P5%a;S267P9PyPz1<{DS0}Q0d#[RD5@zRbQ0:#[S0:=@z{5qzPVQ0:>0Q1D,<D=@z{9qzbC=P|P~bFbGbHX11X21XN1XO1S0:1109S0d/25S10?r;0AE95;S0<1n:;,1;;r9[^11^21^N1^O1S1VP0PBP@Q0z#CS0gQ0z#BS0zQ0mO5b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ1ZQ12PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1EQ267P9PyPzQ1{,<D=@z{9qzbRbPVPbC=P|P~bFbGbHX11X21XN1Q10Q1Y,15;r0Q0<Q1Y,1;;r9[^11^21^N1P0Q1XQ0gQ0zQ0tO4b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ0wQ0~PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PwPxQ1LPyPzQ1OPVQ1OC=P|P~bFbGbHX11RbQ1:Q1P[^11R{P0Q0zQ0pO2b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAQ0|Q11PZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1PbP{P0Q0gPdO2b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAPZPFPGP\PSPHQ0FQ1<Q0AQ1=P=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1Q1DQ25Q24Q1b#fQ1;#fQ09'X'X'X'XQ0X+0r<0CwPxQ1FQ28Q1F7P;7P5Q1FQ29Q1F7P:7P47P9PyPzPzQ0}Q0eQ1[60Q1RyPVPzPzQ0iQ0CPVPzPzQ0BQ1g'<Q0iPVPzPzPvQ0BPVPzPzPyPvPVQ0}Q1s5@zE\E\E\E\E\P|P~bFbGbHX11X21XN1XO1XS1XT1Q0dQ0G,n5'2Q0D,27Q0;=E<4124PQ0G,n4/2<AE74A[[[[[^11^21^N1^O1^S1^T1P0PCPBP@Q0?Q0{#CQ0{#BQ0np+01Ep+01Mp+01QQ1WO;b=bDbCb<b;b:b9b8b3bBb7b6b5b4b0b>b?b@bAbYbjFRFRPaQ13P@P}CTQ14'0ebxbcWvWuP9P0O2n2001000000121000000W0WtP9P0O2n2001000000121000000W0WsP9P0O2n2001000000121000000b0c0>WdXPEPEQ0p9FE_Q1J[^U1^Q1,0OX3EQ0HQ1\P@P}CTQ0o9FE0P2PRP>Q22CT[^PE'0X3EQ0q9FE_RaQ1J[^U1^Q1,0OX3EP0O1P8Q21P@PBP>CNQ1^\a^U1^Q1P2PRP@P}CTQ0q9FE0PXP[P>Q22CT[^PE'0P0PIP@PBPNCNQ0t9FE_Q0>P5Q1ePMCN[^U1^Q1Q17Q1UP@P}CTR}Q0t9FE0PMQ0SP>Q22CT[^PEPZPFPGP\PSPHP=P`P^PTPePUPfPgPhPiPjPkPWP1PKP1PlPnPoP]PpPqPrPsPtPuPmP1PJP1Q0:Q1VP0PBP@%Cc%BcP?O5b=b_bCb<b;b:b9b8bDbBb7b6b5b4b0b>b?b@bAP}eQ02P1P1Q0u9FE0P3PLP>Q22CT[P0Q0x9FE_P4P5P9P0O3Q05Q1|20G59R5#B%C5CTeWdXU1XQ1P9P0O2n200110]00012010\10\XPEH00Y0;Y0<P9P0O2n2001000000121000000W0X3EQ0vQ0kJ1CQ0jQ0sQ0rQ0qQ0pQ0oPcP9Q0mPQQ0hQ0cNS1@c06WwWgP9P0O2n2001000000121000000W0W^P9P0O2n2001000000121000000b0Q0UP?Q0lPYQ0jPQExeY0FWqY08Y09Y07Y04Y03WcY05Y0:Y0?Y0GY0SXf6Z0T1Xk1Y0[W]Y0ZWnY0AWeY0HZ0X1Z0Y1Z0@6L1?Y02Y01P9P0O2n2001000000121000000W0Y00P9P0O2n2001000000121000000W0W~P9P0O2n2001000000121000000W0W}P9P0O2n2001000000121000000W0W|P9P0O2n2001000000121000000W0W{P9P0O2n2001000000121000000W0WzP9P0O2n2001000000121000000W0WyP9P0O2n2001000000121000000c0Ro"). Qed.

End Owners.
End PQOW.

End PnMpOwner.
Module PnRunH.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQRH.

(* [comment removed for export] *)
Definition mparser_init (qc b : Z) : PQM.mpst :=
  PQM.MPST 1 0 0 (PM.SRC qc qc 0) (PM.VShort 0) 0 PQV8.V8Null 0 b 0 [PQM.ms_root].
Definition ast_init (b' : Z) : PQM.ast := PQM.AST [PQM.lv_root] b' 0 (PM.VShort 0) 0 (PM.VShort 0) 0.

(* [comment removed for export] *)
Definition rdr_cost (L : heap_layout) : credit :=
  PM.credit_add (PM.cost1 L PM.CHUNK) (PM.credit_add (PM.cost1 L PQM.PSZ) (PM.cost1 L PQM.LSZ)).

Definition RDRC_H : Z := 7.
Definition PCTOR_H : Z := 6.
Definition ACTOR_H : Z := 2.
Definition RDRD_H : Z := 3.
(* [comment removed for export] *)
Definition RSIZE : Z := 504.

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
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation pm_scr := PMSP.pm_scr.
Abbreviation cfg := (@PMSP.cfg segs).
Abbreviation o_p := (PQR.o_p A).
Abbreviation o_a := (PQR.o_a A AQ).
Abbreviation o_v := (PQR.o_v A).
Abbreviation o_is := (PQR.o_is A).

(* [comment removed for export] *)
Definition opts_at (M : word -> option byte) (oo : Z) : Prop :=
  L5.u64_at segs M oo (pa_vp_opts A) /\ L5.u32_at segs M (oo + 16) PQM.MAX_DEPTH /\ L5.defined M oo 24.
(* [comment removed for export] *)
Definition iss_cells (M : word -> option byte) (ois : Z) : Prop :=
  L5.u64_at segs M ois (pa_vp_iss A) /\ L5.u64_at segs M (ois + 160) (ois + 16).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reader_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (sp r fb oo : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r RDRC_H -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_is fb) -> getr R 12%bv = Z_to_bv 64 (o_v fb) ->
    getr R 13%bv = Z_to_bv 64 oo ->
    fb <= oo -> oo + 24 <= o_p fb -> oo mod 8 = 0 -> opts_at M oo ->
    L5.defined M (o_p fb) RSIZE -> iss_at M (o_is fb) str sm -> PMST.base_ok segs A M -> PMST.loc_ok segs A M true ->
    PMSP.credit_le (rdr_cost L) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (qc b b' : Z) (cr' : credit),
        regs_preserved R R' ->
        mparser_at M' (o_p fb) (o_is fb) (mparser_init qc b) -> adaptor_at M' (o_a fb) (o_v fb) (ast_init b') ->
        L5.u64_at segs M' (o_p fb + qa_off_vref AQ) (o_a fb) ->
        L5C.hpres L LB sp (pm_scr RDRC_H) [(o_p fb, RSIZE)] M M' ->
        PMSP.credit_keep cr cr' (rdr_cost L) PMSP.cr0 ->
        model_but_vm model model' ->
        hi_heap HI (PQR.mown (mparser_init qc b) (ast_init b') ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pa_reader_ctor A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parser_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (sp r fb oo : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r PCTOR_H -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_p fb) -> getr R 11%bv = Z_to_bv 64 (o_is fb) -> getr R 12%bv = Z_to_bv 64 oo ->
    fb <= oo -> oo + 24 <= o_p fb -> oo mod 8 = 0 -> opts_at M oo ->
    L5.defined M (o_p fb) PQM.PSIZE -> iss_cells M (o_is fb) -> PMST.base_ok segs A M -> PMST.loc_ok segs A M true ->
    PMSP.credit_le (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L PQM.PSZ)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (qc b : Z) (cr' : credit),
        regs_preserved R R' ->
        mparser_at M' (o_p fb) (o_is fb) (mparser_init qc b) ->
        L5C.hpres L LB sp (pm_scr PCTOR_H) [(o_p fb, PQM.PSIZE)] M M' ->
        PMSP.credit_keep cr cr' (PM.credit_add (PM.cost1 L PM.CHUNK) (PM.cost1 L PQM.PSZ)) PMSP.cr0 ->
        model_but_vm model model' ->
        hi_heap HI (PQM.mparser_own (mparser_init qc b) ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (qa_parser_ctor AQ) M model) K.

(* [comment removed for export] *)
Definition adaptor_ctor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (sp r fb : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r ACTOR_H -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_a fb) -> getr R 11%bv = Z_to_bv 64 (o_v fb) ->
    L5.defined M (o_a fb) PQM.ASIZE -> PMST.base_ok segs A M ->
    PMSP.credit_le (PM.cost1 L PQM.LSZ) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (b' : Z) (cr' : credit),
        regs_preserved R R' ->
        adaptor_at M' (o_a fb) (o_v fb) (ast_init b') ->
        L5C.hpres L LB sp (pm_scr ACTOR_H) [(o_a fb, PQM.ASIZE)] M M' ->
        PMSP.credit_keep cr cr' (PM.cost1 L PQM.LSZ) PMSP.cr0 ->
        model_but_vm model model' ->
        hi_heap HI (PQM.aown (ast_init b') ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (qa_adaptor_ctor AQ) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reader_dtor_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PQM.mpst) (st : PQM.ast),
    hi_heap HI (PQR.mown s st ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r RDRD_H ->
    frame_ok sp fb -> getr R 10%bv = Z_to_bv 64 (o_p fb) ->
    mparser_at M (o_p fb) (o_is fb) s -> adaptor_at M (o_a fb) (o_v fb) st -> PQM.mgrow_ok s -> PQM.adaptor_ok st ->
    PMST.base_ok segs A M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L LBX sp (pm_scr RDRD_H) [(o_p fb, RSIZE)] M M' ->
        model_but_vm model model' -> hi_heap HI LBX cr M' (m_vmmaps model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (qa_reader_dtor AQ) M model) K.

End Specs.
End PQRH.

End PnRunH.
Module PnHeapP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.PnHeapR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require Export HnIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNHP.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition opnewR_spec_n (NMAX : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> credit_okR cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp PMSR.OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp PMSR.OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pa_opnew A) M model) K.

Lemma opnewR_spec_n_le (N N' : Z) : N' <= N -> opnewR_spec_n N -> opnewR_spec_n N'.
Proof.
  intros HLE OPN fx R M model K LB cr n sp r HH MOK K0 H10 Hn CR H1 RA H2 H4 STK CONT.
  apply (OPN fx R M model K LB cr n sp r HH MOK K0 H10 ltac:(lia) CR H1 RA H2 H4 STK CONT).
Qed.
Lemma opnewR_spec_n_of_R : PMSR.opnewR_spec segs A L HI -> opnewR_spec_n PMSR.NMAXR.
Proof. intros OPN. exact OPN. Qed.

(* [comment removed for export] *)
Definition opnewP_spec (P : NESK.sink_policy) (NMAX : Z) : Prop :=
  NESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> 1 <= fst cr /\ NESK.sp_csz P n <= snd cr ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp PMSR.OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp PMSR.OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (fst cr - 1, snd cr - NESK.sp_csz P n) M' (m_vmmaps model') ->
        NESK.sp_cap P n ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pa_opnew A) M model) K.

(* [comment removed for export] *)
Definition opdelP_spec_at (P : NESK.sink_policy) (pc : Z) : Prop :=
  NESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (B n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    In (B, n) LB -> getr R 10%bv = Z_to_bv 64 B ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp PMSR.OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove B LB) sp PMSR.OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove B LB) (fst cr + 1, snd cr + NESK.sp_csz P n) M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Definition opdelP_spec (P : NESK.sink_policy) : Prop := opdelP_spec_at P (pa_opdel A).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma opnewP_of_RN (zmax hb NMAX : Z) : opnewR_spec_n NMAX -> opnewP_spec (NESK.SP_T zmax hb) NMAX.
Proof.
  intros OPN _ fx R M model K LB cr n sp r HH MOK K0 H10 Hn Hc H1 RA H2 H4 STK CONT.
  apply (OPN fx R M model K LB cr n sp r HH MOK K0 H10 Hn); [exact Hc | exact H1 | exact RA | exact H2 | exact H4 | exact STK |].
  intros fx' R' M' model' B H10' RP FB HP MB HH'.
  apply (CONT fx' R' M' model' B H10' RP FB HP MB); [exact HH' | exact I].
Qed.
Lemma opnewP_of_R (zmax hb : Z) : PMSR.opnewR_spec segs A L HI -> opnewP_spec (NESK.SP_T zmax hb) PMSR.NMAXR.
Proof. intros OPN. apply opnewP_of_RN. exact (opnewR_spec_n_of_R OPN). Qed.

Lemma opdelP_of_R_at (zmax hb pc : Z) : PMSR.opdelR_spec_at segs A L HI pc -> opdelP_spec_at (NESK.SP_T zmax hb) pc.
Proof.
  intros OPD _ fx R M model K LB cr B n sp r HH MOK K0 HIN H10 H1 RA H2 H4 STK CONT.
  apply (OPD fx R M model K LB cr B n sp r HH MOK K0 HIN H10 H1 RA H2 H4 STK).
  intros fx' R' M' model' RP HP MB HH'.
  apply (CONT fx' R' M' model' RP HP MB). exact HH'.
Qed.
Lemma opdelP_of_R (zmax hb : Z) : PMSR.opdelR_spec segs A L HI -> opdelP_spec (NESK.SP_T zmax hb).
Proof. exact (opdelP_of_R_at zmax hb (pa_opdel A)). Qed.

(* [comment removed for export] *)
Lemma PME_nmax_le_NREQ : NESK.sp_nmax NESK.PME <= NREQ.
Proof. unfold NESK.PME, NESK.SP_T, NESK.ZMAX, NREQ. cbn [NESK.sp_nmax]. lia. Qed.
End Specs.
End PNHP.

End PnHeapP.
Module PnSrcGW.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmTxtSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQSW.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition wfill_args (O : PGS.owner) (R : bvmap 5 word) (M : word -> option byte) (sp : Z) (src : PM.srcst) (OB : list (Z * Z)) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK /\ PGS.ow_win O M src OB p PM.CHUNK.
Definition fill_buffer_win_specG : Prop :=
  PGS.src_specG segs A L HI (pa_fill_buffer A) 3 wfill_args (PMTXS.tbfill_W) (PMTXS.tbfill_res).

End Specs.
End PQSW.

End PnSrcGW.
