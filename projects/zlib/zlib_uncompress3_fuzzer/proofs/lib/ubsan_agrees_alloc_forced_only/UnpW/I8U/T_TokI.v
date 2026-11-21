(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Memcpy OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8AdlerIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U8LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require TBase T_It1.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_It0 S_It3 S_It4 S_It5 S_It6.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U Require Base T_It2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_It3.

Module T_It3.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It4.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.Base OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section U8IT3.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.
Definition EXAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => EXA ty p end.
Definition BSAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => BSA ty p end.
Definition FLG (ty : codetype) : Z := match ty with CODES => 0 | _ => 1 end.
Lemma lxor_flag_ne : forall x b, x = 1 -> b = 0 -> Z.lxor x b mod 18446744073709551616 <> 0.
Proof. intros x b -> ->. vm_compute. discriminate. Qed.
Lemma FLG_ne : forall ty, ty <> CODES -> FLG ty = 1.
Proof. intros [] H; [congruence|reflexivity|reflexivity]. Qed.
Lemma b2z_lt1_m : forall a, 1 <= a < 18446744073709551616 -> Z.b2z ((a mod 18446744073709551616) <? 1) = 0.
Proof. intros a H. rewrite Z.mod_small by lia. destruct (a <? 1) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
Lemma b2z_lt1_r : forall a, 1 <= a -> Z.b2z (a <? 1) = 0.
Proof. intros a H. destruct (a <? 1) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
Lemma BSAn_ne : forall ty q, ty <> CODES -> BSAn ty q = BSA ty q.
Proof. intros [] q H; [congruence|reflexivity|reflexivity]. Qed.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).

(* [comment removed for export] *)
Lemma C192 : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.
Proof using C. destruct C; constructor; try assumption. lia_std. Qed.

(* [comment removed for export] *)
Definition pregs8 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\ zget_l R l kA0 = cty ty /\
  zget_l R l kA1 = p + 168 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.
Ltac open_pregs8 H := unfold pregs8 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & g & h & i).
Ltac close_pregs8 := unfold pregs8; split_conj; zreg.

(* [comment removed for export] *)
Definition cregs_t (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs8 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kT2 = it_match ty /\
  zget_l R l kS1 = sp + -136 /\ zget_l R l kS9 = - (sp + -136) + -1.
(* [comment removed for export] *)
Definition sregs_t (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kA6 = lowS (t_low st) /\
  zget_l R l kS6 = t_drop st /\ zget_l R l kT4 = t_sym st /\ zget_l R l kS11 = t_len st /\ zget_l R l kT6 = t_huff st /\
  zget_l R l kT5 = t_used st /\ zget_l R l kS2 = p + 1384 + 4 * t_next st /\ zget_l R l kS10 = t_curr st.
(* [comment removed for export] *)
Definition cmem_t (M : mem) : Prop :=
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 /\ mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get work1Ar) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -200) (2 ^ rt - 1) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -192) (BSAn ty p) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -184) (FLG ty) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -176) (- (p + 808) + -1) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (EXA ty p) (NE ty) (it_extra ty work1Ar) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (BSA ty p) (NE ty) (it_base ty work1Ar) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -208) (EXAn ty p).
Definition smem_t (st : ItSt) (M : mem) : Prop :=
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (arr_get (t_count st)) /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Ltac open_cregs_t H :=
  unfold cregs_t in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let h := fresh "LS0" in let i := fresh "LS8" in
  dand H as (hp & a & b & c & h & i); open_pregs8 hp.
Ltac open_sregs_t H :=
  unfold sregs_t in H;
  let c := fresh "LA6" in let d := fresh "LS5" in
  let e := fresh "LS6" in let f := fresh "LS10" in let g := fresh "LT5" in let h := fresh "LT4" in
  let i := fresh "LS1" in let j := fresh "LS9" in
  dand H as (c & d & e & f & g & h & i & j).
Ltac open_cmem_t H :=
  unfold cmem_t in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f1 := fresh "Hsl8" in let f2 := fresh "Hsl16" in let f3 := fresh "Hsl24" in let f4 := fresh "Hsl32" in
  let h := fresh "Hext" in let i := fresh "Hbase" in let j := fresh "Hz0" in
  dand H as (a & b & c & d & e & f1 & f2 & f3 & f4 & h & i & j).
Ltac open_smem_t H :=
  unfold smem_t in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in dand H as (a & b).
Ltac close_cregs_t := unfold cregs_t; split_conj; try close_pregs8; zreg.
Ltac close_sregs_t := unfold sregs_t; split_conj; zreg.
Ltac close_cmem_t := unfold cmem_t; split_conj; first [assumption | match goal with |- ?g => fail 1 "NOASM" g end].
Ltac close_smem_t := unfold smem_t; split_conj; assumption.
Ltac kauto_t := first
  [ assumption
  | lazymatch goal with
    | |- cregs_t _ _ => close_cregs_t
    | |- sregs_t (tr_st1 _ _) _ _ => fail
    | |- sregs_t (tr_st3 _ _) _ _ => fail
    | |- sregs_t _ _ _ => close_sregs_t
    | |- pregs8 _ _ => close_pregs8
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].

Lemma xaddr_facts_t :
  ZSEP (p + 7160 <= EXA ty p \/ EXA ty p + 2 * NE ty <= p + 1384) /\
  ZSEP (p + 7160 <= BSA ty p \/ BSA ty p + 2 * NE ty <= p + 1384) /\
  0 < EXA ty p /\ EXA ty p + 2 * NE ty <= zc /\   (* [comment removed for export] *)
  0 < BSA ty p /\ BSA ty p + 2 * NE ty <= zc /\ 0 < NE ty <= 288 /\
  EXA ty p mod 2 = 0 /\ BSA ty p mod 2 = 0.
Proof using C ret sp pb wf cf bits nx codes lens_ofs lf.
  pose proof C as C'. open_itc C'. unfold ZSEP in *.
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  destruct ty; cbn [EXA BSA NE]; repeat split; try lia_std; try reflexivity.
  all: try lia_std.
  all: try exact (mod0_add p 808 2 ltac:(lia) P2 ltac:(reflexivity)).
Qed.
Ltac xaddr_t := pose proof xaddr_facts_t as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).
Lemma EXAn_bd : forall ty q, 0 <= EXAn ty q <= 67358.
Proof. intros [] q; cbn [EXAn EXA]; lia. Qed.
Lemma EXAn_ne : forall ty q, ty <> CODES -> EXAn ty q = EXA ty q.
Proof. intros [] q H; [congruence|reflexivity|reflexivity]. Qed.
Lemma lhu_val : forall v, 0 <= v < 65536 -> bytes_le_to_Z (firstn 2 (Z_to_le_bytes (Z.to_nat 2) v)) = v.
Proof.
  intros v Hv. pose proof (bytes_le_Z_to_le_any 2%nat v ltac:(lia)) as E.
  cbn [Z.of_nat] in E. change (2 ^ (8 * 2)) with 65536 in E. rewrite Z.mod_small in E by lia.
  rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; cbn; lia). exact E.
Qed.
Lemma lxor_negI_mod : forall hb b, 0 <= hb <= 15 -> 0 <= b <= 1 -> Z.lxor (-(2 ^ hb)) b mod 18446744073709551616 <> 0.
Proof.
  intros hb b H1 H2.
  assert (Hb : b = 0 \/ b = 1) by lia.
  assert (Hh : hb = 0 \/ hb = 1 \/ hb = 2 \/ hb = 3 \/ hb = 4 \/ hb = 5 \/ hb = 6 \/ hb = 7 \/ hb = 8 \/ hb = 9 \/ hb = 10 \/ hb = 11 \/ hb = 12 \/ hb = 13 \/ hb = 14 \/ hb = 15) by lia.
  clear H1 H2.
  destruct Hb as [Hb | Hb]; subst b.
  - destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    subst hb; intro Hc; vm_compute in Hc; discriminate Hc.
  - destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    destruct Hh as [Hh | Hh]; [ subst hb; intro Hc; vm_compute in Hc; discriminate Hc | ].
    subst hb; intro Hc; vm_compute in Hc; discriminate Hc.
Qed.
Lemma lxor_nz : forall x b, x <> 0 -> x <> 1 -> 0 <= b <= 1 -> Z.lxor x b <> 0.
Proof. intros x b H0 H1 Hb Heq. assert (Hb2 : b = 0 \/ b = 1) by lia. destruct Hb2 as [-> | ->].
  - rewrite Z.lxor_0_r in Heq. contradiction.
  - assert (Hx : x = Z.lxor (Z.lxor x 1) 1) by (rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity).
    rewrite Heq in Hx. rewrite Z.lxor_0_l in Hx. contradiction.
Qed.
Lemma b2z_01 : forall b, 0 <= Z.b2z b <= 1.
Proof. intros []; cbn; lia. Qed.
Lemma lxor_small : forall x b, 0 <= x < 2^47 -> 0 <= b <= 1 -> 0 <= Z.lxor x b < 2^48.
Proof.
  intros x b Hx Hb.
  assert (Hn : 0 <= Z.lxor x b) by (apply Z.lxor_nonneg; lia).
  split; [exact Hn |].
  destruct (Z.eq_dec (Z.lxor x b) 0) as [E|E]; [rewrite E; lia |].
  assert (Hyp : 0 < Z.lxor x b) by lia.
  destruct (Z.eq_dec x 0) as [Ex|Hx0].
  - rewrite Ex, Z.lxor_0_l. assert (b = 0 \/ b = 1) by lia. destruct H as [H0|H0]; subst; cbn; lia.
  - assert (Hxp : 0 < x) by lia.
    pose proof (Z.log2_spec _ Hyp) as [_ Hy].
    assert (Hl : Z.log2 (Z.lxor x b) <= Z.max (Z.log2 x) (Z.log2 b)) by (apply Z.log2_lxor; lia).
    assert (Hb0 : Z.log2 b <= 0).
    { destruct (Z.eq_dec b 0) as [Eb|Eb]; [subst; cbn; lia|].
      assert (b = 1) by lia. subst. cbn. lia. }
    assert (Hlx : Z.log2 x < 47) by (apply Z.log2_lt_pow2; lia).
    assert (Hm : Z.max (Z.log2 x) (Z.log2 b) <= 46) by (apply Z.max_lub; lia).
    assert (HL : 0 <= Z.log2 (Z.lxor x b)) by (apply Z.log2_nonneg).
    assert (Hpow : 2 ^ (Z.log2 (Z.lxor x b) + 1) <= 2 ^ 47) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_add_r, Z.pow_1_r in Hpow by lia. assert (Hy2 : Z.lxor x b < 2 ^ Z.log2 (Z.lxor x b) * 2) by (rewrite Z.mul_comm, <- Z.pow_succ_r by lia; exact Hy).
    assert (Hpow2 : 2 ^ Z.log2 (Z.lxor x b) <= 2 ^ 46) by (apply Z.pow_le_mono_r; lia).
    lia.
Qed.
Lemma lxor_mod_ne : forall x b, x <> 0 -> x <> 1 -> 0 <= x < 2^47 -> 0 <= b <= 1 -> Z.lxor x b mod 18446744073709551616 <> 0.
Proof. intros x b H0 H1 Hx Hb. rewrite Z.mod_small.
  - apply lxor_nz; [exact H0 | exact H1 | exact Hb].
  - pose proof (lxor_small x b Hx Hb). split; [lia | lia].
Qed.

Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma here_t : forall st Rb l M MD T,
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kA2 = p + 808 + 2 * t_sym st -> zget_l Rb l kT1 = tr_hb st ->
  cmem_t M -> SP st ->
  0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall R', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = tr_hb st -> zget_l R' [] kA2 = tr_op X st -> zget_l R' [] kS7 = tr_val X st ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100608 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT2 LT1 HM HU Hsym Hw Hwm HPI K.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. open_cmem_t HM. open_spure HU. zkeys. xaddr_t. pose proof (EXAn_bd ty p) as HXB.
  assert (HBS0 : BSA ty p <> 0) by lia.
  assert (HBS1 : BSA ty p <> 1) by (intro HH; rewrite HH in XBE; vm_compute in XBE; discriminate).
  pose proof (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HWr. pose proof (base_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HBr.
  pose proof (ext_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HEr.
  assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
  unfold tr_w in Hw, Hwm. rewrite WK in Hw, Hwm. box Hwm. clear HtyC HtyD LOWR DROPR Hpb Hprom.
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  zrebase.
  zstep Rfd. zalign.                           (* [comment removed for export] *)
  zbr Rfd false.                               (* [comment removed for export] *)
  tstep Rfd.                                   (* [comment removed for export] *)
  zstep Rfd.                                   (* [comment removed for export] *)
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)) as [Cw1|Cw1'].
  - zbr Rfd false.                             (* [comment removed for export] *)
    zstep Rfd. zstep Rfd.                      (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto_t.
    + zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
    + zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
  - zbr Rfd true.
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))) as [Cw2|Cw2'].
    + zbr Rfd true.                            (* [comment removed for export] *)
      unbox Hwm. specialize (Hwm Cw2).
      assert (Hty : ty <> CODES).
      { intro E. pose proof (HPI E) as HP0. unfold tr_w in HP0. rewrite WK in HP0. rewrite E in HP0, Cw2. cbn [it_match] in HP0, Cw2. lia. }
      rewrite (EXAn_ne ty p Hty) in Hz0. rewrite (BSAn_ne ty p Hty) in Hsl16. pose proof Hsl24 as Hsl24b. rewrite (FLG_ne ty Hty) in Hsl24b. clear Hsl24.
      zstep Rfd. zsetreg (arr_get work1Ar (t_sym st) - it_match ty) ltac:(symmetry; apply swrap32_small; lia).   (* [comment removed for export] *)
      zstep Rfd.                               (* sll *)
      zstep Rfd. zsetreg (2 * (arr_get work1Ar (t_sym st) - it_match ty)) ltac:(pose proof (HWr (t_sym st) ltac:(lia)) as Hb; assert (Hv1 : 0 <= (arr_get work1Ar (t_sym st) - it_match ty)) by lia; assert (Hv2 : (arr_get work1Ar (t_sym st) - it_match ty) < 65536) by lia; rewrite Z.shiftr_div_pow2 by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite (Z.mod_small ((arr_get work1Ar (t_sym st) - it_match ty) * 2 ^ 32) 18446744073709551616) by (split; [nia | nia]); replace ((arr_get work1Ar (t_sym st) - it_match ty) * 2 ^ 32) with ((2 * (arr_get work1Ar (t_sym st) - it_match ty)) * 2 ^ 31) by ring; rewrite Z.div_mul by lia; reflexivity).   (* srl s0 *)
      zstep Rfd.                               (* ld s3,0(sp) *)
      zstep Rfd.                               (* add a2 *)
      zbr Rfd false.                           (* bltu *)
      zstep Rfd.                               (* seqz *)
      zstep Rfd.                               (* ld s4 *)
      zstep Rfd.                               (* xor *)
      pose proof (HWr (t_sym st) ltac:(lia)) as Hb0.
      assert (Hv1 : 0 <= (arr_get work1Ar (t_sym st) - it_match ty)) by lia. assert (Hv2 : (arr_get work1Ar (t_sym st) - it_match ty) < 65536) by lia.
      assert (HBSR : 0 <= BSA ty p < 2^47) by (pose proof XB1; pose proof XB2; pose proof Hsp; pose proof Hsp2; lia).
      let pc := zpc in Rfd pc ltac:(fun F E D => eapply (zu_branch_b false); [zexact F | zexact E | zexact D | zhalted | znorm; cbv beta iota delta [zcond]; apply Z.eqb_neq; apply lxor_flag_ne; [first [reflexivity | apply FLG_ne; exact Hty] | first [ apply b2z_lt1_m | apply b2z_lt1_r ]; pose proof XA1; pose proof XA2; pose proof Hsp; pose proof Hsp2; lia] | ]; zcbv_iota; znorm).
      zstep Rfd.                               (* ld s3,24(sp) *)
      zbr Rfd false.                           (* beqz s3 *)
      zstep Rfd.                               (* ld s3,16(sp) *)
      zstep Rfd.                               (* add s0 *)
      zbr Rfd false.                           (* bltu s0 *)
      zbr Rfd false.                           (* beqz s0 *)
      zstep Rfd.                               (* srl t3 *)
      zstep Rfd. zsetreg (2 * (arr_get work1Ar (t_sym st) - it_match ty)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.shiftr_div_pow2 by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite (Z.mod_small ((arr_get work1Ar (t_sym st) - it_match ty) * 2 ^ 32) 18446744073709551616) by (split; [nia | nia]); rewrite Z.div_mul by lia; ring).   (* sll t3 *)
      zstep Rfd.                               (* ld s0,16(sp) *)
      zstep Rfd.                               (* add t3 *)
      pose proof (mem_arr_get (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (EXA ty p) (NE ty) (it_extra ty work1Ar) (arr_get work1Ar (t_sym st) - it_match ty) Hext ltac:(lia)) as Hmi.
      pose proof (mem_arr_get (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (BSA ty p) (NE ty) (it_base ty work1Ar) (arr_get work1Ar (t_sym st) - it_match ty) Hbase ltac:(lia)) as Hmi2.
      zstep Rfd.                               (* lbu a2 *)
      tstep Rfd.                               (* lhu s7 *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto_t.
      all: try kauto_t.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. try rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. cbn [fst]. symmetry. apply wrap8_mod.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. try rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. cbn [snd]. apply lhu_val. apply HBr. lia.
    + zbr Rfd false.                           (* [comment removed for export] *)
      zstep Rfd. zstep Rfd. zstep Rfd.         (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto_t.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. try rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. try rewrite WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_shiftl_add : forall x y k, 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y -> Z.lor x (Z.shiftl y k) = x + Z.shiftl y k.
Proof using.
  intros x y k Hk Hx Hy.
  assert (L0 : Z.land x (Z.shiftl y k) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n k).
    - rewrite Z.shiftl_spec_low by lia_std. apply Bool.andb_false_r.
    - destruct (Z.eq_dec x 0) as [->|]; [rewrite Z.bits_0; reflexivity|].
      rewrite (Z.bits_above_log2 x n); [reflexivity | lia_std |].
      apply Z.log2_lt_pow2; [lia_std|]. eapply Z.lt_le_trans; [apply (proj2 Hx) | apply Z.pow_le_mono_r; lia_std]. }
  pose proof (Z.add_lor_land x (Z.shiftl y k)). lia_std.
Qed.

(* [comment removed for export] *)
Lemma entry_write2_t : forall M base n f i pk val a0 a2,
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base i f ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u16 (run_segments R_segs rc_inp rc_sp rc_mb) M a0 pk -> mem_u16 (run_segments R_segs rc_inp rc_sp rc_mb) M a2 val ->
  a0 = base + 4 * i -> a2 = a0 + 2 -> 0 <= i < n -> base + 4 * n <= two64 -> 0 <= base -> 0 <= val < 65536 ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base n (zfupd f i (pk mod 65536 + 65536 * val)).
Proof using.
  intros M base n f i pk val a0 a2 H1 H2 Hlo Hhi -> -> Hi Hn Hb Rv.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  change 4%nat with (2 + 2)%nat. rewrite Z_to_le_bytes_add. unfold mem_u16 in *.
  pose proof (Z.mod_pos_bound pk 65536 ltac:(lia)) as PM.
  apply mem_is_app; [| | rewrite two64_eq in *; lia | rewrite !length_Z_to_le_bytes; cbn; rewrite two64_eq in *; lia].
  - rewrite <- Z_to_le_bytes_2_mod. replace ((pk mod 65536 + 65536 * val) mod 65536) with (pk mod 65536); [rewrite Z_to_le_bytes_2_mod; exact Hlo|].
    rewrite Z.mul_comm, Z_mod_plus_full. rewrite Z.mod_mod by lia. reflexivity.
  - rewrite length_Z_to_le_bytes. change (Z.of_nat 2) with 2.
    replace (Z.shiftr (pk mod 65536 + 65536 * val) (8 * 2)) with val; [exact Hhi|].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 2)) with 65536. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fill_loop_t : forall trips f t n st pk Rb l M MD T,
  f = 2 ^ tr_hb st * Z.of_nat trips -> (1 <= trips)%nat -> Z.of_nat trips <= n ->
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = 256 * tr_hb st -> zget_l Rb l kS4 = 2 ^ t_curr st ->
  zget_l Rb l kA2 = f -> zget_l Rb l kS5 = - 2 ^ tr_hb st -> zget_l Rb l kS0 = tr_hd st + (f - 2 ^ tr_hb st) ->
  zget_l Rb l kS7 = pk -> zget_l Rb l kS3 = tr_val X st -> zget_l Rb l kT3 = 1 ->
  pk mod 65536 + 65536 * tr_val X st = tr_here X st ->
  0 <= tr_hb st <= 15 -> 0 <= t_next st -> 0 <= tr_hd st -> t_next st + tr_hd st + f - 2 ^ tr_hb st < 1444 ->
  0 <= tr_val X st < 65536 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get t) -> arr_len t = 1444 ->
  (forall R' M', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = 256 * tr_hb st -> zget_l R' [] kS4 = 2 ^ t_curr st ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get (snd (loopZ n (fill_body (tr_here X st) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (f, t)))) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100732 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100672 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction trips as [|trips IH]; intros f t n st pk Rb l M MD T Hf Htr Hn Hh HC HS LT1 LS4 LT2 LT3 LT6 LS7 LS3 LS2 EPK Hhb Hnx0 Hhd Hfit Rval Wp Htbl TL K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI.
  set (I := 2 ^ tr_hb st) in *.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  assert (Hf1 : I <= f) by (rewrite Hf; apply mul_S_ge; lia).
  assert (W1 : wrap32 (f - I) = f - I) by (apply wrap32_small; lia).
  destruct (arr4_hole (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) Htbl ltac:(lia)) as [HT1 HT2].
  clear Htbl. zrebase.
  zstep Rfd.                                                                      (* [comment removed for export] *)
  zstep Rfd. zsetreg (4 * (tr_hd st + (f - I))) ltac:(symmetry; apply zext32_x4; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                                      (* [comment removed for export] *)
  zbr Rfd false.                                                                  (* [comment removed for export] *)
  assert (HIp : 1 <= I) by (unfold I; apply Z.le_trans with (2 ^ 0); [cbn; lia | apply Z.pow_le_mono_r; lia]).
  zstep Rfd. zstep Rfd.
  zsetreg 1 ltac:(rewrite Z.mod_small by lia; destruct (Z.ltb_spec (4 * (tr_hd st + (f - I)) + (p + 1384 + 4 * t_next st)) 1); [lia | reflexivity]).
  zbr Rfd false.
  zstep Rfd. zsetreg (f - I) ltac:(symmetry; apply swrap32_small; lia).          (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_hd st + (f - I)) ltac:(symmetry; apply zext32_id; lia). (* [comment removed for export] *)
  zstep Rfd. zsetreg (4 * (tr_hd st + (f - I))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                                      (* [comment removed for export] *)
  zstep Rfd.                                                                      (* [comment removed for export] *)
  zstep Rfd.                                                                      (* [comment removed for export] *)
  match goal with
  | Hlo : mem_u16 _ ?Mc _ pk, Hv : mem_u16 _ _ _ (tr_val X st) |- _ =>
    pose proof (entry_write2_t Mc (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) pk _ _ _ HT1 HT2 Hlo Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) Rval) as Htbl;
    clear Hlo Hv HT1 HT2
  end.
  rewrite EPK in Htbl.
  apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
  replace (t_next st + tr_hd st + (f - I)) with (t_next st + (tr_hd st + wrap32 (f - I))) in Htbl by lia.
  zstep Rfd. zsetreg (tr_hd st + (f - I - I)) ltac:(lia).                        (* [comment removed for export] *)
  destruct (Z.eq_dec (f - I) 0) as [Hz|Hnz].
  - zbr Rfd false.                                                                (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
    all: try kauto_t.
    rewrite fill_last by first [lia | rewrite W1; exact Hz]. cbn [snd]. rewrite W1, Hz in Htbl. exact Htbl.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (f - I) (arr_set t (t_next st + (tr_hd st + wrap32 (f - I))) (tr_here X st)) (n - 1) st pk Rx [] Mx MD T) end.
    all: try kauto_t.
    all: try (rewrite Hf; apply mul_S_sub).
    all: try (rewrite arr_len_set; exact TL).
    all: try (zregv; subst I; lia).
    all: try (destruct trips; [cbn in Hf; exfalso; lia | lia]).
    intros R' M'. intros. eapply K; try eassumption.
    * eapply mpost_trans; [exact HAG | assumption].
    * rewrite fill_more by first [lia | rewrite W1; exact Hnz]. subst I. rewrite W1 in *. assumption.
Qed.

Lemma op_val_range_t : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  0 <= tr_op X st < 256 /\ 0 <= tr_val X st < 65536.
Proof using C zc ret sp pb p cf. intros. eapply op_val_range; try eassumption. exact C192. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fill_t : forall st Rb l M MD T,
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = tr_hb st ->
  zget_l Rb l kA2 = tr_op X st -> zget_l Rb l kS7 = tr_val X st ->
  SP st -> it_trip_ok X 288 320 1444 st = true ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)) ->
  (forall R' M', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = 256 * tr_hb st -> zget_l R' [] kS4 = 2 ^ t_curr st ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100732 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100608 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 LT2 LS7 HU TOK Wp Htbl K.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. open_spure HU. zkeys.
  trip_facts TOK.
  unbox Fwm. pose proof (op_val_range_t st WK Fw Fwm) as [Rop Rval].
  clear Fwm Flook Fcont LOWR DROPR Hprom HtyC HtyD Hlf Hcf Hwf HCr HTr Hpb Hlens15.
  assert (Ehb : tr_hb st = t_len st - t_drop st) by reflexivity.
  assert (Hhb : 0 <= tr_hb st <= 15) by lia.
  assert (Hhd : 0 <= tr_hd st <= t_huff st).
  { unfold tr_hd. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (t_drop st) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PF.
  pose proof (pow2_le15 (t_curr st - tr_hb st) ltac:(lia)) as PQ.
  assert (EQ : 2 ^ t_curr st = 2 ^ tr_hb st * 2 ^ (t_curr st - tr_hb st)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hfit' : t_next st + tr_hd st + 2 ^ t_curr st - 2 ^ tr_hb st < 1444) by (unfold tr_hd; rewrite Ehb; exact Ffit).
  assert (FI : 2 ^ tr_hb st <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
  set (pk := tr_op X st + 256 * tr_hb st + 65536 * tr_val X st).
  assert (EPK : pk mod 65536 + 65536 * tr_val X st = tr_here X st).
  { unfold tr_here. rewrite (wrap8_mod (tr_hb st)). rewrite (Z.mod_small (tr_hb st)) by lia.
    rewrite code_pack_small by lia. subst pk.
    replace (tr_op X st + 256 * tr_hb st + 65536 * tr_val X st) with (tr_op X st + 256 * tr_hb st + tr_val X st * 65536) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia. }
  zrebase.
  zstep Rfd.                                                                                   (* [comment removed for export] *)
  zbr Rfd false.                                                                               (* [comment removed for export] *)
  zstep Rfd.                                                                                   (* [comment removed for export] *)
  zstep Rfd. zsetreg (- 2 ^ tr_hb st) ltac:(symmetry; apply sllw_m1; lia).                    (* [comment removed for export] *)
  zstep Rfd.                                                                                   (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 ^ t_curr st) ltac:(symmetry; apply sllw_1; lia).                     (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_hd st) ltac:(unfold tr_hd; symmetry; apply srlw_small; lia).          (* [comment removed for export] *)
  zstep Rfd.                                                                                   (* [comment removed for export] *)
  zstep Rfd. zsetreg (256 * tr_hb st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).           (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_op X st + 256 * tr_hb st)
    ltac:(replace (256 * tr_hb st) with (Z.shiftl (tr_hb st) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
          rewrite lor_shiftl_add by (try (change (2 ^ 8) with 256); lia); rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                                                   (* [comment removed for export] *)
  zstep Rfd. zsetreg pk
    ltac:(rewrite Z.lor_comm, lor_shiftl_add by (try (change (2 ^ 16) with 65536); lia); rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; subst pk; lia).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_hd st + (2 ^ t_curr st - 2 ^ tr_hb st)) ltac:(lia).                 (* [comment removed for export] *)
  zstep Rfd. zsetreg 1 ltac:(rewrite Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 1384 + 4 * t_next st)); [reflexivity | lia]).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_val X st)
    ltac:(rewrite srli_small by (subst pk; lia); change (2 ^ 16) with 65536; subst pk;
          replace (tr_op X st + 256 * tr_hb st + 65536 * tr_val X st) with (tr_val X st * 65536 + (tr_op X st + 256 * tr_hb st)) by lia;
          rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia).                       (* [comment removed for export] *)
  zstep Rfd.                                                                                   (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (fill_loop_t (Z.to_nat (2 ^ (t_curr st - tr_hb st))) (2 ^ t_curr st) (t_tbl st) (2 ^ t_curr st) st pk Rx [] M MD T) end.
  all: try kauto_t.
  all: try exact EPK.
  - rewrite Z2Nat.id by lia. exact EQ.
  - lia.
  - rewrite Z2Nat.id by lia. apply Z.pow_le_mono_r; lia.
  - lia.
  - intros R' M'. intros. eapply K; try eassumption.
    unfold tr_tbl1. rewrite it_fill_eq. unfold tr_incr, tr_fill. rewrite !shl32_1 by lia. assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma incr_loop_t : forall m c n st Rb l M MD T,
  0 <= c < 2 ^ Z.of_nat m -> Z.of_nat m < n -> c < 65536 ->
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = 256 * tr_hb st -> zget_l Rb l kS4 = 2 ^ t_curr st ->
  zget_l Rb l kT3 = c -> 0 <= t_huff st < 65536 ->
  (forall R', cregs_t R' [] -> sregs_t st R' [] -> zget_l R' [] kT1 = 256 * tr_hb st -> zget_l R' [] kS4 = 2 ^ t_curr st ->
     zget_l R' [] kA2 = loopZ n (incr_body (t_huff st)) c ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100772 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100752 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  induction m as [|m IH]; intros c n st Rb l M MD T Hc Hn Hc2 Hh HC HS LT1 LS4 LT3 Hhuff K.
  - cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hc. assert (E : c = 0) by lia. rewrite E in *. clear E Hc Hc2.
    pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hpb.
    zrebase. zstep Rfd. zstep Rfd. zsetreg 0 ltac:(rewrite Z.land_0_l; reflexivity).
    zstep Rfd. zsetreg 0 ltac:(reflexivity). zstep Rfd. zsetreg 0 ltac:(reflexivity).
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto_t. zregv. symmetry. apply incr_last; [lia | apply Z.land_0_r].
  - pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hpb.
    assert (HA : 0 <= Z.land c (t_huff st) <= c) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
    pose proof (shiftr1_half c m Hc) as HH.
    assert (HH2 : Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; apply Z.div_le_upper_bound; lia).
    zrebase.
    zstep Rfd.                                                        (* [comment removed for export] *)
    zstep Rfd.                                                        (* [comment removed for export] *)
    zstep Rfd. zsetreg (Z.land c (t_huff st)) ltac:(symmetry; apply swrap32_small; lia).   (* [comment removed for export] *)
    zstep Rfd. zsetreg (Z.shiftr c 1) ltac:(transitivity (c / 2 ^ 1); [rewrite Z.shiftr_div_pow2 by lia; reflexivity | symmetry; apply srliw_small; lia]).   (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.land c (t_huff st)) 0) as [Z0|NZ].
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto_t. zregv. symmetry. apply incr_last; [lia | rewrite Z.land_comm; exact Z0].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (Z.shiftr c 1) (n - 1) st Rx [] M MD T) end.
      all: try kauto_t. all: try lia.
      intros R' HC' HS' L1 L4 L2. eapply K; try eassumption. rewrite incr_more; [exact L2 | lia | rewrite Z.land_comm; exact NZ].
Qed.

(* [comment removed for export] *)
Ltac close_sregs1_t EL := unfold sregs_t; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.

(* [comment removed for export] *)
Definition Ksub_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregs_t R' [] -> sregs_t (tr_st1 X st) R' [] ->
    zget_l R' [] kS4 = 2 ^ t_curr st -> zget_l R' [] kS0 = Z.shiftl (tr_sym st) 32 ->
    mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 -> cmem_t M' -> smem_t (tr_st1 X st) M' ->
    tr_brk X st = false ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100932 (zupd R' []) M' MD) T.
Definition Kbrk_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregs_t R' [] -> sregs_t (tr_st1 X st) R' [] ->
    zget_l R' [] kT1 = 256 * tr_hb st ->
    mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 -> cmem_t M' -> smem_t (tr_st1 X st) M' ->
    tr_brk X st = true ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101212 (zupd R' []) M' MD) T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma count_t : forall st Rb l M MD T,
  m_halted MD = None -> cregs_t Rb l -> sregs_t st Rb l -> zget_l Rb l kT1 = 256 * tr_hb st -> zget_l Rb l kS4 = 2 ^ t_curr st ->
  cmem_t M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (arr_get (t_count st)) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
  Ksub_t st M MD T -> Kbrk_t st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100732 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 LS4 HM HU TOK Hcnt Htbl KS KB.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_sregs_t HS. open_cmem_t HM. open_spure HU. zkeys. xaddr_t.
  trip_facts TOK. clear Fcont Fwm Hprom HtyC HtyD Hcf Hwf DROPR.
  pose proof (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192) as HWr.
  pose proof (mx15 lf lens_ofs codes) as MXR.
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  pose proof (lnot_val_mod' (sp + -136) ltac:(lia)) as Hn8.
  pose proof (lnot_val_mod' (p + 808) ltac:(lia)) as Hnw.
  pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL.
  zrebase.
  zstep Rfd. zsetreg (t_len st - 1) ltac:(symmetry; apply swrap32_small; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zbr Rfd false.                                                             (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 ^ (t_len st - 1)) ltac:(symmetry; apply sllw_1; lia).    (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (incr_loop_t (Z.to_nat (t_len st)) (2 ^ (t_len st - 1)) 32 st Rx [] M MD T) end.
  all: try kauto_t.
  { rewrite Z2Nat.id by lia. split; [lia|]. apply Z.pow_lt_mono_r; lia. }
  { lia. }
  { assert (2 ^ (t_len st - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  clear_regs. intros R1 HC HS L1 L4 L2.
  assert (EI : loopZ 32 (incr_body (t_huff st)) (2 ^ (t_len st - 1)) = tr_incr2 st).
  { unfold tr_incr2. rewrite it_incr_back_eq, shl32_1 by lia. reflexivity. }
  pose proof (incr_range (t_huff st) 32 (2 ^ (t_len st - 1)) ltac:(lia)) as IR.
  rewrite EI in L2, IR. clear EI.
  assert (I14 : 2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
  set (v1 := Z.land (tr_incr2 st - 1) (t_huff st) + tr_incr2 st).
  assert (HL : 0 <= Z.land (tr_incr2 st - 1) (t_huff st) <= t_huff st).
  { destruct (Z.eq_dec (tr_incr2 st) 0) as [E0|NE0].
    - rewrite E0. change (0 - 1) with (-1). rewrite Z.land_m1_l. lia.
    - split; [apply Z.land_nonneg; lia | apply land_le_r; lia]. }
  assert (EH : tr_huff st = Z.land (Z.b2z (tr_incr2 st =? 0) + -1) v1).
  { unfold tr_huff, v1. destruct (Z.eqb_spec (tr_incr2 st) 0) as [E0|NE0]; cbn [Z.b2z negb Z.add].
    - symmetry. apply Z.land_0_l.
    - rewrite Z.land_m1_l. rewrite Z.land_comm. reflexivity. }
  set (c0 := arr_get (t_count st) (t_len st)).
  pose proof (HCr (t_len st) ltac:(lia)) as HC0. fold c0 in HC0.
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  open_cregs_t HC. open_sregs_t HS. zkeys. zrebase.
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zbr Rfd false.                                                             (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 * t_len st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
  zbr Rfd false.                                                             (* [comment removed for export] *)
  zstep Rfd. zsetreg (Z.b2z (tr_incr2 st =? 0))
    ltac:(rewrite (Z.mod_small (tr_incr2 st)) by lia; destruct (Z.eqb_spec (tr_incr2 st) 0); destruct (Z.ltb_spec (tr_incr2 st) 1); cbn [Z.b2z]; lia).  (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_sym st) ltac:(rewrite ESY; lia).                   (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  tstep Rfd.                                                                 (* [comment removed for export] *)
  fold c0. set (c0s := bv_swrap 16 c0) in *.
  pose proof (swrap16_cases c0 HC0) as HS16. fold c0s in HS16.
  assert (HSR : -32768 <= c0s <= c0) by (destruct HS16; lia). box HS16.
  zstep Rfd. zsetreg v1 ltac:(unfold v1; symmetry; apply swrap32_small; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zstep Rfd. zsetreg (-281474976710656) ltac:(reflexivity).                 (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_huff st) ltac:(exact EH).                           (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  tstore_arr Rfd Hcnt (t_len st).                                            (* [comment removed for export] *)
  assert (Hcnt' : forall Mq, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (sp + -136) 16 (zfupd (arr_get (t_count st)) (t_len st) (c0s + -1)) ->
                             mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (sp + -136) 16 (arr_get (tr_count st))).
  { intros Mq Hq. eapply mem_arr_ext_mod; [exact Hq|]. intros j Hj. unfold tr_count, zfupd, tr_c. fold c0.
    change (cell_mod 2) with 65536. rewrite arr_get_set. unfold arr_inb. rewrite CL.
    destruct (Z.eqb_spec j (t_len st)) as [Ej|NEj].
    - subst j. rewrite Z.eqb_refl. destruct (Z.leb_spec 0 (t_len st)); destruct (Z.ltb_spec (t_len st) 16); cbn [andb]; try lia.
      rewrite wrap16_mod. rewrite Z.mod_mod by lia. unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B; [f_equal; lia|].
      replace (c0 - 65536 + -1) with ((c0 - 1) + (-1) * 65536) by lia. rewrite Z_mod_plus_full. reflexivity.
    - destruct (Z.eqb_spec (t_len st) j); [lia|]. cbn [andb]. reflexivity. }
  apply Hcnt' in Hcnt. clear Hcnt'.
  assert (EC : tr_c st = (c0 - 1) mod 65536) by (unfold tr_c; fold c0; apply wrap16_mod).
  zstep Rfd. zsetreg ((c0s + -1) * 281474976710656) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 48) with 281474976710656; lia).  (* [comment removed for export] *)
  zstep Rfd.                                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (Z.eq_dec c0 1) as [C1|NC1].
  - assert (C1s : c0s = 1) by (unbox HS16; destruct HS16; lia).
    zbr Rfd false.
    assert (EC0 : tr_c st = 0) by (rewrite EC, C1; reflexivity).
    (* [comment removed for export] *)
    destruct (Z.eq_dec (t_len st) mx) as [LM|NLM].
    + zbr Rfd true.
      assert (EL : tr_len X st = t_len st).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [reflexivity | lia]. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB Rx Mx) end.
      all: try kauto_t.
      * close_sregs1_t EL.
      * close_cmem_t.
      * unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_eq. exact LM.
    + zbr Rfd false.
      unbox Flook. dand (Flook EC0 NLM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. rewrite <- ESY in W1, W2, W3, W4.
      zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).   (* [comment removed for export] *)
      zstep Rfd.                                                        (* [comment removed for export] *)
      zbr Rfd false.                                                    (* [comment removed for export] *)
      zstep Rfd.                                                        (* [comment removed for export] *)
      zstep Rfd. zalign.                                                (* [comment removed for export] *)
      zbr Rfd false.                                                    (* [comment removed for export] *)
      tstep Rfd.                                                        (* [comment removed for export] *)
      zstep Rfd. zsetreg (2 * arr_get work1Ar (tr_sym st)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
      zstep Rfd.                                                        (* [comment removed for export] *)
      zbr Rfd false.                                                    (* [comment removed for export] *)
      zstep Rfd. zstep Rfd. zstep Rfd.                                  (* [comment removed for export] *)
      zsetreg 1 ltac:(rewrite !Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 168 + 2 * lens_ofs)); [|lia];
                      destruct (Z.ltb_spec (p + 168 + 2 * lens_ofs + 2 * arr_get work1Ar (tr_sym st)) 1); [lia|]; reflexivity).
      zbr Rfd false.                                                    (* [comment removed for export] *)
      zbr Rfd false.                                                    (* [comment removed for export] *)
      zstep Rfd. zalign.                                                (* [comment removed for export] *)
      zbr Rfd false.                                                    (* [comment removed for export] *)
      tstep Rfd.                                                        (* [comment removed for export] *)
      assert (EL : tr_len X st = lf (lens_ofs + arr_get work1Ar (tr_sym st))).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [lia|].
        cbn [andb negb]. rewrite WK. apply lensA_get. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
      all: try kauto_t.
      * close_sregs1_t EL.
      * close_cmem_t.
      * unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_neq. exact NLM.
  - assert (HNZ : ((c0s + -1) * 281474976710656) mod 18446744073709551616 <> 0).
    { unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B.
      - destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia].
      - rewrite negshift48_mod by lia. lia. }
    zbr Rfd true.
    assert (ECN : tr_c st <> 0).
    { rewrite EC. destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia]. }
    assert (EL : tr_len X st = t_len st).
    { unfold tr_len. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity]. }
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
    all: try kauto_t.
    * close_sregs1_t EL.
    * close_cmem_t.
    * unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
    * unfold tr_brk. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
Qed.
End U8IT3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_pregs8 H := unfold pregs8 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & g & h & i).
Ltac close_pregs8 := unfold pregs8; split_conj; zreg.
Ltac open_cregs_t H :=
  unfold cregs_t in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let h := fresh "LS0" in let i := fresh "LS8" in
  dand H as (hp & a & b & c & h & i); open_pregs8 hp.
Ltac open_sregs_t H :=
  unfold sregs_t in H;
  let c := fresh "LA6" in let d := fresh "LS5" in
  let e := fresh "LS6" in let f := fresh "LS10" in let g := fresh "LT5" in let h := fresh "LT4" in
  let i := fresh "LS1" in let j := fresh "LS9" in
  dand H as (c & d & e & f & g & h & i & j).
Ltac open_cmem_t H :=
  unfold cmem_t in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f1 := fresh "Hsl8" in let f2 := fresh "Hsl16" in let f3 := fresh "Hsl24" in let f4 := fresh "Hsl32" in
  let h := fresh "Hext" in let i := fresh "Hbase" in let j := fresh "Hz0" in
  dand H as (a & b & c & d & e & f1 & f2 & f3 & f4 & h & i & j).
Ltac open_smem_t H :=
  unfold smem_t in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in dand H as (a & b).
Ltac close_cregs_t := unfold cregs_t; split_conj; try close_pregs8; zreg.
Ltac close_sregs_t := unfold sregs_t; split_conj; zreg.
Ltac close_cmem_t := unfold cmem_t; split_conj; assumption.
Ltac close_smem_t := unfold smem_t; split_conj; assumption.
Ltac close_sregs1_t EL := unfold sregs_t; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.
Ltac kauto_t := first
  [ assumption
  | lazymatch goal with
    | |- cregs_t _ _ _ _ _ _ _ _ _ _ _ _ => close_cregs_t
    | |- sregs_t _ (tr_st1 _ _) _ _ => fail
    | |- sregs_t _ (tr_st3 _ _) _ _ => fail
    | |- sregs_t _ _ _ _ => close_sregs_t
    | |- pregs8 _ _ _ _ _ _ _ _ _ => close_pregs8
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].
Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.
End T_It3.

Module T_It4.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It4.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.Base OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It2 T_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section U8IT4.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregs_t ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs_t p).
#[local] Abbreviation CM := (cmem_t ty lf lens_ofs codes nx bits wf p sp).
#[local] Abbreviation SM := (smem_t p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).
#[local] Abbreviation C192' := (C192 ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).

(* [comment removed for export] *)
Definition uregs_t (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT4 = tr_sym st /\ zget_l R l kS11 = tr_len X st /\ zget_l R l kT6 = tr_huff st /\
  zget_l R l kS0 = Z.shiftl (tr_sym st) 32 /\ zget_l R l kS8 = tr_low X st.
Ltac open_uregs_t H :=
  unfold uregs_t in H;
  let a := fresh "LS6" in let b := fresh "LS10" in let d := fresh "LT5" in
  let e := fresh "LT6" in let g := fresh "LS7" in
  dand H as (a & b & d & e & g).
Ltac close_uregs_t := unfold uregs_t; split_conj; zreg.
Ltac kauto4 := first
  [ assumption
  | lazymatch goal with
    | |- uregs_t _ _ _ => close_uregs_t
    | |- _ => kauto_t
    end ].
Ltac xaddr_t := pose proof (xaddr_facts_t _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).

(* [comment removed for export] *)
Ltac zbr_by bv tac :=
  let pc := zpc in Rfd pc ltac:(fun F E D => eapply (zu_branch_b bv); [exact F | exact E | exact D | zhalted | znorm; tac | ]; cbv iota; znorm).

(* [comment removed for export] *)
Lemma entry_write_t : forall M base n f i op hbits val a0 a1 a2,
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base i f ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a0 op -> mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a1 hbits -> mem_u16 (run_segments R_segs rc_inp rc_sp rc_mb) M a2 val ->
  a0 = base + 4 * i -> a1 = a0 + 1 -> a2 = a0 + 2 ->
  0 <= i < n -> base + 4 * n <= two64 -> 0 <= base ->
  0 <= op < 256 -> 0 <= hbits < 256 -> 0 <= val < 65536 ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M base n (zfupd f i (code_pack op hbits val)).
Proof using.
  intros M base n f i op hbits val a0 a1 a2 H1 H2 Ho Hb Hv -> -> -> Hi Hn Hb0 Ro Rb Rv.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  apply mem_arr4_pack; try assumption; rewrite ?two64_eq in *; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma curr_loop_t : forall m curr lft n (cnt : arr) st (vused vs1 vt1 : Z) Rb l M MD T,
  mx - (curr + rt) <= Z.of_nat m -> Z.of_nat m < n -> 1 <= mx ->
  1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
  (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kT5 = vused -> zget_l Rb l kS2 = vs1 -> zget_l Rb l kA2 = vt1 -> zget_l Rb l kS7 = rt ->
  zget_l Rb l kA6 = curr + rt -> zget_l Rb l kT1 = lft -> zget_l Rb l kS10 = mx - rt ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 (arr_get cnt) ->
  (forall R', CR R' [] -> uregs_t st R' [] -> zget_l R' [] kT5 = vused -> zget_l R' [] kS2 = vs1 -> zget_l R' [] kA2 = vt1 -> zget_l R' [] kS7 = rt ->
     zget_l R' [] kS10 = fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101072 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101020 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction m as [|m IH]; intros curr lft n cnt st vused vs1 vt1 Rb l M MD T Hm Hn Hmx Hc1 Hcm Hl HCR Hh HC HUr LT4 LS1 LT1 LRA LA6 LT2 LS9 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_uregs_t HUr. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' ltac:(lia)) as (RT1 & RT2 & RT3).
  assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
  pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
  pose proof (lnot_val_mod' (sp + -136) ltac:(lia)) as Hn8.
  zrebase.
  zstep Rfd. zsetreg (2 * (curr + rt)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
  zbr Rfd false.                                               (* [comment removed for export] *)
  zstep Rfd.                                                   (* [comment removed for export] *)
  tstep Rfd.                                                   (* [comment removed for export] *)
  zstep Rfd. zsetreg (lft - arr_get cnt (curr + rt)) ltac:(symmetry; apply swrap32_small; lia).   (* [comment removed for export] *)
  destruct (Z_lt_le_dec 0 (lft - arr_get cnt (curr + rt))) as [GT|LE].
  - zbr Rfd false.                                             (* [comment removed for export] *)
    zstep Rfd. zsetreg 0 ltac:(symmetry; rewrite srliw_small by lia; apply Z.div_small; change (2 ^ 30) with 1073741824; lia).   (* [comment removed for export] *)
    zbr Rfd false.                                             (* [comment removed for export] *)
    zstep Rfd. zsetreg (curr + rt + 1) ltac:(symmetry; apply swrap32_small; lia).   (* [comment removed for export] *)
    zstep Rfd. zsetreg (2 * (lft - arr_get cnt (curr + rt))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
    destruct (Z_lt_le_dec (curr + rt + 1) mx) as [MORE|DONE].
    + zbr Rfd true.                                            (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) cnt st vused vs1 vt1 Rx [] M MD T) end.
      all: try kauto4.
      all: try lia.
      all: try (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
      intros R' HC' HU' L4 L1 LT1' LR L9. eapply K; try eassumption.
        rewrite curr_more by lia; rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia;
          replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia; assumption.
    + zbr Rfd false.
      zstep Rfd.                                               (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto4.
      zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. lia.
  - zbr Rfd true.                                              (* [comment removed for export] *)
    zstep Rfd. zsetreg curr ltac:(rewrite swrap32_small by lia; lia).   (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto4.
    zregv. rewrite curr_stop_le by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition Kbody3_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', CR R' [] -> SR (tr_st3 X st) R' [] ->
     zget_l R' [] kT1 = tr_len X st - tr_drop X st -> zget_l R' [] kA2 = p + 808 + 2 * tr_sym st ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 -> CM M' -> SM (tr_st3 X st) M' ->
     tr_sub X st = true -> it_not_enough ty (tr_used X st) = false ->
     1 <= tr_curr X st <= 15 -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd R' []) M' MD) T.
Definition Kfail_t (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', CR R' [] -> zget_l R' [] kA6 = 1 -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = true ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M MD) T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma link_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kS7 = rt -> zget_l Rb l kS10 = tr_curr X st ->
  zget_l Rb l kT5 = tr_used X st -> zget_l Rb l kA2 = p + 1384 + 4 * tr_next st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = false -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_len X st <= 15 ->
  Kbody3_t st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101136 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LRA LS9 LT4 LT1 HM HSM HP TOK Hbrk Hsub Hne Hmx HLOW HDR TLR K3.
  pose proof C as C'. open_itc C'. open_cregs_t HC. open_uregs_t HU. open_cmem_t HM. open_smem_t HSM. open_spure HP. zkeys. xaddr_t.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  trip_facts TOK. clear Flook Fwm LOWR DROPR Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  assert (HST3 : it_step X st = ItCont (tr_st3 X st)).
  { rewrite it_step_eq. rewrite Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity. }
  unbox Fcont. dand (Fcont (tr_st3 X st) HST3) as (Flow3 & Fcurr3 & Fnext3).
  { right. cbn [t_next tr_st3]. unfold tr_next, tr_fill. rewrite shl32_1 by lia. pose proof (pow2_le15 (t_curr st) ltac:(lia)). lia. }
  cbn [t_low t_curr t_next tr_st3] in Flow3, Fcurr3, Fnext3. clear Fcont HST3.
  assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
  pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC. pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (Hroom3 : t_next st < 1444).
  { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
    assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  assert (P2 : p mod 2 = 0) by (apply mod0_16_2; exact Hpal).
  pose proof (lnot_val_mod' (p + 808) ltac:(lia)) as Hnw.
  destruct (arr4_hole (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.                                                           (* [comment removed for export] *)
  zstep Rfd. zsetreg (4 * tr_low X st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  zbr Rfd false.                                                       (* [comment removed for export] *)
  zstep Rfd. zstep Rfd. zstep Rfd.                                     (* [comment removed for export] *)
  zsetreg 1 ltac:(rewrite !Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 1384 + 4 * nx)); [|lia];
                  destruct (Z.ltb_spec (p + 1384 + 4 * nx + 4 * tr_low X st) 1); [lia|]; reflexivity).
  zbr Rfd false.                                                       (* [comment removed for export] *)
  zbr Rfd false.                                                       (* [comment removed for export] *)
  zstep Rfd. zalign.                                                   (* [comment removed for export] *)
  zbr Rfd false.                                                       (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  zbr Rfd false.                                                       (* [comment removed for export] *)
  zstep Rfd. zsetreg (4 * (tr_next st - nx)) ltac:(rewrite swrap32_small by lia; lia).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_next st - nx) ltac:(rewrite srli_small by lia; change (2 ^ 2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).   (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_curr X st), Hb : mem_u8 _ _ _ rt, Hv : mem_u16 _ _ _ (tr_next st - nx) |- _ =>
    pose proof (entry_write_t Mc (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite it_fill_len_tr; lia].
  zstep Rfd.                                                           (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_len X st - rt) ltac:(rewrite swrap32_small by lia; lia).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).   (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  zstep Rfd. zstep Rfd.                                                (* [comment removed for export] *)
  zstep Rfd.                                                           (* [comment removed for export] *)
  zbr Rfd false.                                                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K3 Rx Mx) end.
  all: try kauto4.
  all: lazymatch goal with
       | |- sregs_t _ _ _ _ => unfold sregs_t; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st3]; rewrite HDR;
                               rewrite (lowS_small (tr_low X st)) by lia; split_conj; zreg
       | |- zget_l _ _ _ = _ => zregv; rewrite ?HDR; lia
       | |- cmem_t _ _ _ _ _ _ _ _ _ _ => close_cmem_t
       | |- smem_t _ _ _ _ => unfold smem_t; cbn [t_count t_tbl tr_st3]; split; [exact Hcnt|]; unfold tr_tbl2; cbn [x_table x_root itm_ctx]; exact Htbl
       | |- _ => lia
       end.
Qed.

Lemma snez_cty1 : Z.b2z (0 <? (cty ty + -1) mod 18446744073709551616) = 1 - isL ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.
Lemma seqz_cty2 : Z.b2z ((cty ty + -2) mod 18446744073709551616 <? 1) = isD ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma enough_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kS7 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kS10 = tr_curr X st -> zget_l Rb l kA2 = p + 1384 + 4 * tr_next st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_curr X st <= 15 -> 1 <= tr_len X st <= 15 ->
  Kbody3_t st M MD T -> Kfail_t st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101080 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LRA LT4 LS9 LT1 HM HSM HP TOK Hbrk Hsub Hmx HLOW HDR HCU TLR K3 KF.
  pose proof C as C'. open_itc C'. open_cmem_t HM. open_spure HP. zkeys.
  trip_facts TOK. clear Flook Fwm Fcont Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
  { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
  pose proof (ne_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192') as (IL & ID & ILD & NE').
  open_cregs_t HC. open_uregs_t HU. zkeys. zrebase.
  zstep Rfd.                                                          (* [comment removed for export] *)
  zstep Rfd.                                                          (* [comment removed for export] *)
  zstep Rfd. zsetreg (1 - isL ty) ltac:(symmetry; apply snez_cty1).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 ^ tr_curr X st) ltac:(symmetry; apply sllw_1; lia).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (tr_used X st) ltac:(rewrite EU, swrap32_small by lia; lia).   (* [comment removed for export] *)
  zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).   (* [comment removed for export] *)
  destruct IL as [IL0|IL1].
  - (* [comment removed for export] *)
    zstep Rfd. zsetreg 1 ltac:(rewrite IL0; destruct (tr_used X st <? 853); reflexivity).   (* [comment removed for export] *)
    zbr Rfd false.                                                    (* [comment removed for export] *)
    zstep Rfd.                                                        (* [comment removed for export] *)
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).   (* [comment removed for export] *)
    zstep Rfd. zsetreg (isD ty) ltac:(symmetry; apply seqz_cty2).    (* [comment removed for export] *)
    zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).   (* [comment removed for export] *)
    destruct ID as [ID0|ID1].
    + zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).   (* [comment removed for export] *)
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_t st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      * unfold cmem_t; split_conj; assumption.
      * unfold spure; split_conj; assumption.
      * rewrite NE', IL0, ID0. reflexivity.
    + zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite ID1; symmetry; apply land1_b2z).   (* [comment removed for export] *)
      destruct (Z.leb_spec 593 (tr_used X st)) as [GE|LT].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
        all: try kauto4. rewrite NE', IL0, ID1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_t st Rx [] M MD T) end.
        all: try kauto4. all: try assumption. all: try lia.
        -- unfold cmem_t; split_conj; assumption.
        -- unfold spure; split_conj; assumption.
        -- rewrite NE', IL0, ID1. cbn [Z.eqb]. apply Z.ltb_ge. lia.
  - (* [comment removed for export] *)
    assert (ID0 : isD ty = 0) by lia.
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite IL1; cbn [Z.sub Z.pos_sub]; destruct (tr_used X st <? 853); reflexivity).   (* [comment removed for export] *)
    destruct (Z.ltb_spec (tr_used X st) 853) as [LT|GE].
    + zbr Rfd false.
      zstep Rfd.                                                      (* [comment removed for export] *)
      zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
      zstep Rfd. zsetreg (isD ty) ltac:(symmetry; apply seqz_cty2).
      zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
      zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_t st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      * unfold cmem_t; split_conj; assumption.
      * unfold spure; split_conj; assumption.
      * rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_ge. lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
      all: try kauto4. rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma currsz_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs_t st Rb l -> zget_l Rb l kS7 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kA2 = p + 1384 + 4 * tr_next st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  1 <= tr_len X st <= 15 -> rt < tr_len X st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3_t st M MD T -> Kfail_t st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100988 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LRA LT4 LT1 HM HSM HP TOK Hbrk Hsub Hmx TLR RTL HLOW HDR K3 KF.
  pose proof C as C'. open_itc C'. open_smem_t HSM. open_spure HP. zkeys.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  pose proof (tr_count_range st HCr) as HCr1.
  set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
  pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
  assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
  { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
    fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
  pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
  rewrite <- ETC in CR1, CR2, CR3.
  open_cregs_t HC. open_uregs_t HU. zkeys. zrebase.
  zstep Rfd. zsetreg c0 ltac:(rewrite swrap32_small by lia; lia).             (* [comment removed for export] *)
  zstep Rfd.                                                                (* [comment removed for export] *)
  zbr Rfd false.                                                            (* [comment removed for export] *)
  destruct (Z_lt_le_dec (tr_len X st) mx) as [LT|GE].
  - zbr Rfd false.                                                          (* [comment removed for export] *)
    zstep Rfd.                                                              (* [comment removed for export] *)
    zstep Rfd. zsetreg (2 ^ c0) ltac:(symmetry; apply sllw_1; lia).          (* [comment removed for export] *)
    zstep Rfd. zsetreg (mx - rt) ltac:(rewrite swrap32_small by lia; lia).   (* [comment removed for export] *)
    zstep Rfd.                                                              (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (curr_loop_t 15%nat c0 (2 ^ c0) 16 (tr_count st) st (t_used st) _ (p + 1384 + 4 * tr_next st) Rx [] M MD T) end.
    all: try kauto4. all: try lia. all: try (zregv; reflexivity).
    clear_regs. intros R' HC' HU' L4 L1 LT1' LR L9. rewrite <- ETC in L9. specialize (CR2 ltac:(lia)).
    open_cregs_t HC'. open_uregs_t HU'. zkeys. zrebase.
    zstep Rfd.                                                              (* [comment removed for export] *)
    zbr Rfd false.                                                          (* [comment removed for export] *)
    eapply enough_t; try eassumption; try lia. all: try kauto4.
    + unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
  - zbr Rfd true.                                                           (* [comment removed for export] *)
    assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (enough_t st Rx [] M MD T) end.
    all: try kauto4. all: try (rewrite ETC0; zreg). all: try lia.
    + unfold smem_t. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sub_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR (tr_st1 X st) Rb l -> zget_l Rb l kS4 = 2 ^ t_curr st -> zget_l Rb l kS0 = Z.shiftl (tr_sym st) 32 ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> 1 <= mx ->
  (forall R', CR R' [] -> SR (tr_st1 X st) R' [] ->
     zget_l R' [] kT1 = tr_len X st - t_drop st -> zget_l R' [] kA2 = p + 808 + 2 * tr_sym st ->
     tr_sub X st = false ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd R' []) M MD) T) ->
  Kbody3_t st M MD T -> Kfail_t st M MD T ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100932 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS4 LT6 HM HSM HP TOK Hbrk Hmx K1 K3 KF.
  pose proof C as C'. open_itc C'. open_spure HP. pose proof HM as HM'. open_cmem_t HM'. zkeys. xaddr_t.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  trip_facts TOK. clear Fwm Fcont.
  pose proof (pow2_le15 rt ltac:(lia)) as PRT. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC.
  assert (TLR : 1 <= tr_len X st <= 15).
  { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
    destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
    destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
    unbox Flook. dand (Flook E0 NEM) as (W1 & W2 & W3 & W4).
    replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). exact W4. }
  clear Flook.
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  assert (HHF : 0 <= tr_huff st).
  { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
    pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
    rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
    destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
    assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
  assert (HLOW : 0 <= tr_low X st < 32768).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia.
    split; [apply Z.land_nonneg; lia|]. eapply Z.le_lt_trans; [apply land_le_r; lia | lia]. }
  assert (ELOW : Z.land (tr_huff st) (2 ^ rt - 1) = tr_low X st).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia. reflexivity. }
  assert (HDR : tr_drop X st = rt).
  { unfold tr_drop. cbn [x_root itm_ctx]. unbox DROPR. destruct DROPR as [D0|D1]; rewrite D0 || rewrite D1; [reflexivity|].
    destruct (Z.eqb_spec rt 0); lia. }
  assert (Hroom3 : t_next st < 1444).
  { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
    assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
  assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
  pose proof (lnot_val_mod' (p + 808) ltac:(lia)) as Hnw.
  (* [comment removed for export] *)
  assert (JB : forall RJ, CR RJ [] -> SR (tr_st1 X st) RJ [] -> zget_l RJ [] kS0 = Z.shiftl (tr_sym st) 32 ->
            tr_sub X st = false -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100440 (zupd RJ []) M MD) T).
  { intros RJ HCJ HSJ JT6 Hsub. open_cregs_t HCJ. open_sregs_t HSJ.
    cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LA6, LS5, LS6, LS10, LT5, LT4, LS1, LS9. zkeys. zrebase.
    zstep Rfd. zstep Rfd.                                   (* [comment removed for export] *)
    zstep Rfd. zsetreg (tr_len X st - t_drop st) ltac:(rewrite swrap32_small by lia; lia).   (* [comment removed for export] *)
    zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).   (* [comment removed for export] *)
    zstep Rfd.                                              (* [comment removed for export] *)
    zstep Rfd. zstep Rfd.                                   (* [comment removed for export] *)
    zstep Rfd.                                              (* [comment removed for export] *)
    zbr Rfd false.                                          (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
    all: try kauto4.
    unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg. }
  (* [comment removed for export] *)
  assert (J04 : forall RJ, CR RJ [] -> uregs_t st RJ [] -> zget_l RJ [] kS6 = t_drop st -> zget_l RJ [] kT5 = t_used st ->
            zget_l RJ [] kS2 = p + 1384 + 4 * t_next st -> zget_l RJ [] kS4 = 2 ^ t_curr st ->
            tr_sub X st = true -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100952 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ JS5 JT4 JS1 JS4 Hsub.
    assert (RTL : rt < tr_len X st).
    { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
    assert (JDC : forall RK, CR RK [] -> uregs_t st RK [] -> zget_l RK [] kS7 = rt -> zget_l RK [] kT5 = t_used st ->
              zget_l RK [] kS2 = p + 1384 + 4 * t_next st -> zget_l RK [] kS4 = 2 ^ t_curr st ->
              realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100964 (zupd RK []) M MD) T).
    { intros RK HCK HUK KRA KT4 KS1 KS4. open_cregs_t HCK. open_uregs_t HUK. zkeys. zrebase.
      zbr Rfd false.                                        (* [comment removed for export] *)
      zstep Rfd.                                            (* [comment removed for export] *)
      zstep Rfd. zsetreg (4 * 2 ^ t_curr st) ltac:(symmetry; apply zext32_x4; lia).   (* [comment removed for export] *)
      zstep Rfd. zsetreg (p + 1384 + 4 * tr_next st) ltac:(rewrite ENX; lia).        (* [comment removed for export] *)
      zbr Rfd false.                                        (* [comment removed for export] *)
      zbr Rfd false.                                        (* [comment removed for export] *)
      eapply currsz_t; try eassumption; try lia. all: try kauto4.
      unfold spure; split_conj; try assumption. }
    open_cregs_t HCJ. open_uregs_t HUJ. zkeys. zrebase.
    zstep Rfd.                                              (* [comment removed for export] *)
    unbox DROPR. destruct DROPR as [D0|D1].
    - zbr Rfd true.                                         (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JDC Rx) end.
      all: try kauto4.
    - zbr Rfd false.
      zstep Rfd.                                            (* [comment removed for export] *)
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JDC Rx) end.
      all: try kauto4. }
  open_cregs_t HC. open_sregs_t HS. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LA6, LS5, LS6, LS10, LT5, LT4, LS1, LS9.
  zkeys. zrebase.
  destruct (Z_lt_le_dec rt (tr_len X st)) as [SUB1|NOSUB1].
  - zbr Rfd false.                                          (* [comment removed for export] *)
    zstep Rfd.                                              (* [comment removed for export] *)
    zstep Rfd. zsetreg (tr_low X st) ltac:(exact (eq_sym ELOW)).   (* [comment removed for export] *)
    unbox LOWR. destruct LOWR as [LM|LSM].
    + (* [comment removed for export] *)
      zstep Rfd. zsetreg (-1) ltac:(unfold lowS; rewrite LM; reflexivity).   (* [comment removed for export] *)
      zbr_by false ltac:(cbv beta iota delta [zcond]; rewrite (mod_small_u64 (tr_low X st)) by lia;
                         try change ((-1) mod 18446744073709551616) with 18446744073709551615; apply Z.eqb_neq; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx) end.
      all: try kauto4.
      unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
      replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
    + zstep Rfd. zsetreg (t_low st) ltac:(rewrite (lowS_small (t_low st)) by lia; rewrite swrap32_small by lia; lia).   (* [comment removed for export] *)
      destruct (Z.eq_dec (tr_low X st) (t_low st)) as [EQL|NEL].
      * zbr Rfd true.                                       (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JB Rx) end.
        all: try kauto4.
        -- unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
        -- unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, EQL, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx) end.
        all: try kauto4.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  - zbr Rfd true.                                           (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JB Rx) end.
    all: try kauto4.
    + unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
    + unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End U8IT4.
End T_It4.

Module T_It5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It5.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.Base OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It2 T_It3 T_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section U8IT5.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregs_t ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs_t p).
#[local] Abbreviation CM := (cmem_t ty lf lens_ofs codes nx bits wf p sp).
#[local] Abbreviation SM := (smem_t p sp).
#[local] Abbreviation C192' := (C192 ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

(* [comment removed for export] *)


Ltac xaddr := pose proof (xaddr_facts_t _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).

(* [comment removed for export] *)
Lemma cmem_mpost : forall M M' lo hi,
  CM M -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' lo hi 0 0 ->
  ((lo = p + 1384 /\ hi = p + 7160) \/ (lo = sp + -136 /\ hi = sp + -104)) -> CM M'.
Proof using C zc ret pb cf.
  intros M M' lo hi HM [HA HW] Hr. pose proof C as C'. open_itc C'. xaddr. unfold ZSEP in *. open_cmem_t HM.
  unfold cmem_t. split_conj.
  - apply HW. exact Wf.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl8 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl16 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl24 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hsl32 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hext | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hbase | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hz0 | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
Qed.

Lemma cnt_mpost : forall M M' f, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 f -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -136) 16 f.
Proof using C zc ret pb wf cf bits nx codes lens_ofs lf ty.
  intros M M' f H [HA HW]. pose proof C as C'. open_itc C'.
  eapply mem_arr_magree; [exact HA | exact H | lia_std | lia_std].
Qed.
(* [comment removed for export] *)

Lemma mpostL_of_tbl : forall M M', mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (p + 1384) (p + 7160) 0 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsL p sp).
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M M M' (rsL p sp) _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (rsL p sp)) HP) as H.
  apply H; [left | right; lia]. cbn. right. left. lia.
Qed.
Lemma mpostL_of_cnt : forall M M', mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -136) (sp + -104) 0 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsL p sp).
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M M M' (rsL p sp) _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (rsL p sp)) HP) as H.
  apply H; [left | right; lia]. cbn. left. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma trip_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kT1 = t_len st - t_drop st -> zget_l Rb l kA2 = p + 808 + 2 * t_sym st ->
  CM M -> SM st M -> SP st ->
  it_trip_ok X 288 320 1444 st = true -> 1 <= mx -> (ty = CODES -> tr_w st < it_match ty) ->
  (forall st' R' M', it_step X st = ItCont st' -> CR R' [] -> SR st' R' [] ->
      zget_l R' [] kT1 = t_len st' - t_drop st' -> zget_l R' [] kA2 = p + 808 + 2 * t_sym st' ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsL p sp) -> CM M' -> SM st' M' -> SP st' ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItBreak st' -> CR R' [] -> SR st' R' [] -> zget_l R' [] kT1 = 256 * (t_len st' - t_drop st') ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsL p sp) -> CM M' -> SM st' M' -> SP st' ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101212 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItFail st' -> CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsL p sp) -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 LT2 HM HSM HP TOK Hmx HPI KC KB KF.
  pose proof HP as HP'. open_spure HP'. open_smem_t HSM.
  pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm.
  eapply here_t; try eassumption; try lia.
  intros R1 HC1 HS1 L1 L2 L7.
  eapply fill_t; try eassumption.
  { open_cmem_t HM. assumption. }
  intros R2 M2 HC2 HS2 L1' L4 HPO1 Wp2 Htbl2.
  pose proof (cmem_mpost M M2 _ _ HM HPO1 ltac:(left; split; reflexivity)) as HM2.
  pose proof (cnt_mpost M M2 _ Hcnt HPO1) as Hcnt2.
  eapply count_t; try eassumption.
  - (* [comment removed for export] *)
    intros R3 M3 HC3 HS3 L4' L6 HPO2 HM3 HSM3 Hbrk.
    eapply sub_t; try eassumption.
    + (* [comment removed for export] *)
      intros R4 HC4 HS4 L1'' L2'' Hsub. eapply (KC (tr_st1 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * apply spure_st1. exact HP.
    + (* [comment removed for export] *)
      intros R4 M4 HC4 HS4 L1'' L2'' HPO3 HM4 HSM4 Hsub Hne HCU HLOW HDR HNX. eapply (KC (tr_st3 X st) R4 M4); try assumption.
      all: try (rewrite it_step_eq, Hbrk, Hsub; cbn [x_ty itm_ctx]; rewrite Hne; reflexivity).
      all: try (cbn [t_len t_drop tr_st3]; exact L1'').
      all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 |];
                eapply mpostL_trans; [apply mpostL_of_cnt; exact HPO2 | apply mpostL_of_tbl; exact HPO3]).
      all: apply spure_st3; assumption.
    + (* [comment removed for export] *)
      intros R4 HC4 LA6 Hsub Hne. eapply (KF (tr_st2 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * cbn [t_tbl tr_st2]. apply tr_tbl1_range. exact HTr.
  - (* [comment removed for export] *)
    intros R3 M3 HC3 HS3 L1'' HPO2 HM3 HSM3 Hbrk.
    assert (EL : tr_len X st = t_len st).
    { unfold tr_brk in Hbrk. apply andb_prop in Hbrk as [B1 B2]. unfold tr_len. rewrite B1.
      cbn [x_max itm_ctx] in *. rewrite B2. reflexivity. }
    assert (HHF : 0 <= tr_huff st).
    { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
      pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
      rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
      destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
      assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
    eapply (KB (tr_st1 X st) R3 M3); try assumption.
    all: try (rewrite it_step_eq, Hbrk; reflexivity).
    all: try (cbn [t_len t_drop tr_st1]; rewrite EL; first [exact L1'' | lia]).
    all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2]).
    all: try (apply spure_st1; exact HP).
    all: cbn [t_used t_huff tr_st1]; first [exact HHF | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main_loop_t : forall (PI : ItSt -> Prop),
  (forall st, PI st -> ty = CODES -> tr_w st < it_match ty) ->
  (forall st st', PI st -> it_step X st = ItCont st' -> PI st') ->
  forall k st Rb l M0 M MD T,
  it_loop_ok k X 288 320 1444 st = true -> 1 <= mx -> PI st ->
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kT1 = t_len st - t_drop st -> zget_l Rb l kA2 = p + 808 + 2 * t_sym st ->
  CM M -> SM st M -> SP st ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (rsL p sp) ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inl st' ->
      CR R' [] -> SR st' R' [] -> zget_l R' [] kT1 = 256 * (t_len st' - t_drop st') ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M' (rsL p sp) -> CM M' -> SM st' M' -> SP st' ->
      (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444) ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101212 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inr st' ->
      CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M' (rsL p sp) -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros PI HI1 HI2. induction k as [|k IH]; intros st Rb l M0 M MD T HOK Hmx PIs Hh HC HS LT1 LT2 HM HSM HP HPL KB KF.
  { cbn [it_loop_ok] in HOK. discriminate. }
  rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
  eapply trip_t; try eassumption.
  - exact (HI1 _ PIs).
  - intros st' R' M' Hstep HC' HS' LT1' LT2' HPO HM' HSM' HP'. rewrite Hstep in REST.
    eapply (IH st' R' [] M0 M' MD T); try eassumption.
    + eapply HI2; eassumption.
    + eapply mpostL_trans; eassumption.
    + intros st'' R'' M'' Hl. eapply KB. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
    + intros st'' R'' M'' Hl. eapply KF. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
  - intros st' R' M' Hstep HC' HS' L8 HPO HM' HSM' HP' B1 B2 B3. rewrite Hstep in REST.
    eapply KB; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
    + intros Hne. destruct (Z.eqb_spec (t_huff st') 0); [lia_std|]. cbn [negb] in REST.
      apply andb_prop in REST as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia_std.
  - intros st' R' M' Hstep HC' LA6 HPO HM' HSM' HW HTR. eapply KF; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
Qed.
End U8IT5.
End T_It5.

Module T_It6.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It6.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.Base OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It2 T_It3 T_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section U8IT6.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation PR6 := (pregs6_t ty lens_ofs p pb sp vgp vtp).
#[local] Abbreviation PR8 := (pregs8 ty lens_ofs p pb sp vgp vtp).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregs_t ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs_t p).
#[local] Abbreviation CM := (cmem_t ty lf lens_ofs codes nx bits wf p sp).
#[local] Abbreviation SM := (smem_t p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).
#[local] Abbreviation C192' := (C192 ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C).

Ltac xaddr_t := pose proof (xaddr_facts_t _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN & XAE & XBE).
Ltac close_pregs6_t := unfold pregs6_t; split_conj; zreg.
Ltac open_pregs6_t H := unfold pregs6_t in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & g & h & i).

(* [comment removed for export] *)
Definition slots_t (M : mem) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z) : Prop :=
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -8) v1 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -16) v8 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -24) v9 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -32) v18 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -40) v19 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -48) v20 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -56) v21 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -64) v22 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -72) v23 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -80) v24 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -88) v25 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -96) v26 /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -104) v27.

(* [comment removed for export] *)
Definition pregs3_t (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp.
Ltac close_pregs3_t := unfold pregs3_t; split_conj; zreg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma init_t : forall Rb l M MD T,
  m_halted MD = None -> PR8 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  zget_l Rb l kT2 = it_match ty -> zget_l Rb l kA6 = 1 -> zget_l Rb l kS2 = p + 1384 + 4 * nx ->
  1 <= mx ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get work1Ar) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -192) (BSAn ty p) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -184) (FLG ty) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (EXA ty p) (NE ty) (it_extra ty work1Ar) -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (BSA ty p) (NE ty) (it_base ty work1Ar) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -208) (EXAn ty p) ->
  SM st0 M ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> zget_l R' [] kT1 = t_len st0 - t_drop st0 -> zget_l R' [] kA2 = p + 808 + 2 * t_sym st0 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -208) (sp + -168) 0 0 -> CM M' -> SM st0 M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100376 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LA2 LA6 LS1 Hmx Wf Wp Hlens Hwork Hnext Hsl16 Hsl24 Hext Hbase Hz0 HSM K.
  pose proof C as C'. open_itc C'. open_pregs8 HP. open_smem_t HSM. zkeys. xaddr_t. clear Hprom HtyC HtyD Hpb.
  cbn [t_count t_tbl itm_st0] in Hcnt, Htbl.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3). pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -208) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -208) (sp + -168) 0 0) M) by (apply mpost_refl).
  zrebase.
  zbr Rfd false.                                          (* [comment removed for export] *)
  zstep Rfd. zstep Rfd. zstep Rfd.                        (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).          (* [comment removed for export] *)
  zstep Rfd.                                              (* [comment removed for export] *)
  zstep Rfd. znot.                                        (* [comment removed for export] *)
  zstep Rfd.                                              (* [comment removed for export] *)
  zstep Rfd.                                              (* [comment removed for export] *)
  zstep Rfd. zsetreg (2 ^ rt - 1) ltac:(rewrite swrap32_small by lia; lia). (* [comment removed for export] *)
  zstep Rfd.                                              (* [comment removed for export] *)
  zstep Rfd. znot.                                        (* [comment removed for export] *)
  zstep Rfd. zstep Rfd. zstep Rfd.                        (* [comment removed for export] *)
  zstep Rfd.                                              (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  - close_cregs_t.
  - unfold sregs_t. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low itm_st0]. rewrite itm_used_pow2 by lia.
    unfold lowS. cbn [Z.eqb Pos.eqb]. split_conj; zreg.
  - cbn [t_len t_drop itm_st0]. zreg.
  - cbn [t_sym itm_st0]. zreg.
  - exact HAG.
  - unfold cmem_t. split_conj; assumption.
  - unfold smem_t. cbn [t_count t_tbl itm_st0]. split; assumption.
Qed.

Lemma ty_cases_t :
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty p = p + 808 /\ BSA ty p = p + 808 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty p = 67232 /\ BSA ty p = 67170 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty p = 67358 /\ BSA ty p = 67294 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma p144_al : (p + 160) mod 2 ^ 3 = 0.
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf ty.
  pose proof C as C'. open_itc C'. change (2 ^ 3) with 8.
  assert (D : exists q, p = 16 * q). { apply Z.mod_divide in Hpal; [|lia_std]. destruct Hpal as [q Hq]. exists q. lia_std. }
  destruct D as [q ->]. replace (16 * q + 160) with ((2 * q + 20) * 8) by lia_std. apply Z_mod_mult.   (* a worker 1.4: next at 160 *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma switch_t : forall Rb l M MD T,
  m_halted MD = None -> PR6 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt -> 1 <= mx ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get work1Ar) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67170 31 (arr_get lbase_a) -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67232 31 (arr_get lext_a) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67294 32 (arr_get dbase_a) -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67358 32 (arr_get dext_a) ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> zget_l R' [] kT1 = t_len st0 - t_drop st0 -> zget_l R' [] kA2 = p + 808 + 2 * t_sym st0 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -208) (sp + -168) 0 0 ->
     CM M' -> SM st0 M' -> SP st0 -> it_not_enough ty (itm_used rt) = false ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100476 (zupd R' []) M' MD) T) ->
  (forall R' M', PR8 R' [] -> zget_l R' [] kA6 = 1 -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -208) (sp + -168) 0 0 ->
     it_not_enough ty (itm_used rt) = true ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100188 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde KBODY KFAIL.
  pose proof C as C'. open_itc C'. open_pregs6_t HP. zkeys. xaddr_t. clear HtyC HtyD.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as (RT1 & RT2 & RT3).
  pose proof (spure_st0 _ _ _ _ _ _ _ _ _ _ _ _ _ C192' Hmx) as HSP.
  pose proof p144_al as P8.
  assert (HSM : forall Mq, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (sp + -136) 16 cA -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 1384) 1444 cf -> SM st0 Mq).
  { intros Mq A B. unfold smem_t. cbn [t_count t_tbl itm_st0]. split; [exact A|].
    eapply mem_arr_ext; [exact B|]. intros j _. symmetry. apply tblA_get. }
  pose proof (ne_pow _ _ _ _ _ _ _ _ _ _ _ _ _ C192' rt ltac:(lia)) as NEP.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -208) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -208) (sp + -168) 0 0) M) by (apply mpost_refl).
  (* [comment removed for export] *)
  assert (J : forall RJ MJ, PR8 RJ [] -> zget_l RJ [] kT0 = mx -> zget_l RJ [] kT1 = mn -> zget_l RJ [] kA7 = rt ->
            zget_l RJ [] kT2 = it_match ty ->
            framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -208) (sp + -168) 0 0) MJ ->
            mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MJ p 7176 ->
            mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 808) 288 (arr_get work1Ar) ->
            mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp + -136) 16 cA -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 1384) 1444 cf ->
            mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 160) (p + 1384 + 4 * nx) ->
            mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp + -192) (BSAn ty p) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp + -184) (FLG ty) ->
            mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (EXA ty p) (NE ty) (it_extra ty work1Ar) -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (BSA ty p) (NE ty) (it_base ty work1Ar) ->
            mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp + -208) (EXAn ty p) ->
            realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100320 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JT0 JT1 JA7 JA2 HAGJ WfJ WpJ HlensJ HworkJ HcntJ HtblJ HnextJ Hs16 Hs24 HextJ HbaseJ HzJ.
    clear Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde HAG. open_pregs8 HPJ. zkeys. zrebase.
    zbr Rfd false.                                       (* [comment removed for export] *)
    zstep Rfd. zsetreg 0 ltac:(symmetry; apply (land_mask0 (p + 160) 3); [lia_std | exact P8]).   (* [comment removed for export] *)
    zbr Rfd false.                                       (* [comment removed for export] *)
    zstep Rfd.                                           (* [comment removed for export] *)
    zbr Rfd false.                                       (* [comment removed for export] *)
    zstep Rfd.                                           (* [comment removed for export] *)
    zstep Rfd.                                           (* [comment removed for export] *)
    destruct ty_cases_t as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
      rewrite E0 in LA0.
    - (* [comment removed for export] *)
      zbr Rfd true.                                      (* [comment removed for export] *)
      zstep Rfd.                                         (* [comment removed for export] *)
      zbr Rfd true.                                      (* [comment removed for export] *)
      eapply init_t; try eassumption; try lia.
      all: try kauto_t. all: try (zregv; rewrite E0; reflexivity).
      + apply HSM; assumption.
      + intros R' M' HC' HS' L1 L2 HPO HM' HSM'. eapply KBODY; try eassumption.
        * eapply mpost_trans; [exact HAGJ | exact HPO].
        * rewrite NEP, Ety. reflexivity.
    - (* [comment removed for export] *)
      zbr Rfd false.                                     (* [comment removed for export] *)
      zstep Rfd.                                         (* [comment removed for export] *)
      destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
      + zbr Rfd true.                                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx MJ) end.
        all: try kauto_t. all: try exact HAGJ.
        rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
      + zbr Rfd false.
        zstep Rfd.                                       (* [comment removed for export] *)
        zbr Rfd true.                                    (* [comment removed for export] *)
        eapply init_t; try eassumption; try lia.
        all: try kauto_t. all: try (zregv; rewrite E0; reflexivity).
        * apply HSM; assumption.
        * intros R' M' HC' HS' L1 L2 HPO HM' HSM'. eapply KBODY; try eassumption.
          -- eapply mpost_trans; [exact HAGJ | exact HPO].
          -- rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
    - (* [comment removed for export] *)
      zbr Rfd true.                                      (* [comment removed for export] *)
      zstep Rfd.                                         (* [comment removed for export] *)
      zbr Rfd false.                                     (* [comment removed for export] *)
      zstep Rfd.                                         (* [comment removed for export] *)
      destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
      + zbr Rfd true.                                    (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx MJ) end.
        all: try kauto_t. all: try exact HAGJ.
        rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
      + zbr Rfd false.
        eapply init_t; try eassumption; try lia.
        all: try kauto_t. all: try (zregv; rewrite E0; reflexivity).
        * apply HSM; assumption.
        * intros R' M' HC' HS' L1 L2 HPO HM' HSM'. eapply KBODY; try eassumption.
          -- eapply mpost_trans; [exact HAGJ | exact HPO].
          -- rewrite NEP, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia]. }
  zrebase.
  destruct ty_cases_t as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
    rewrite E0 in LA0.
  - zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try kauto_t. all: try (zregv; first [rewrite EM | rewrite E0]; reflexivity).
    all: rewrite ?EX, ?EB, ?EN, ?Ety; try assumption.
    all: try (cbn [EXAn BSAn FLG EXA BSA]; try assumption).
  - zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try kauto_t. all: try (zregv; first [rewrite EM | rewrite E0]; reflexivity).
    all: rewrite ?EX, ?EB, ?EN, ?Ety; try assumption.
    all: try (cbn [EXAn BSAn FLG EXA BSA]; try assumption).
  - zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try kauto_t. all: try (zregv; first [rewrite EM | rewrite E0]; reflexivity).
    all: rewrite ?EX, ?EB, ?EN, ?Ety; try assumption.
    all: try (cbn [EXAn BSAn FLG EXA BSA]; try assumption).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma epilogue_t : forall Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  m_halted MD = None -> zget_l Rb l kSP = sp + -208 -> zget_l Rb l kA6 = v ->
  slots_t M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> Z.land v1 (-2) = v1 -> 0 <= v1 < two64 ->
  (forall R', zget_l R' [] kA0 = v -> zget_l R' [] kSP = sp -> zget_l R' [] kRA = v1 ->
     zget_l R' [] kS0 = v8 -> zget_l R' [] kS1 = v9 -> zget_l R' [] kS2 = v18 -> zget_l R' [] kS3 = v19 ->
     zget_l R' [] kS4 = v20 -> zget_l R' [] kS5 = v21 -> zget_l R' [] kS6 = v22 -> zget_l R' [] kS7 = v23 ->
     zget_l R' [] kS8 = v24 -> zget_l R' [] kS9 = v25 -> zget_l R' [] kS10 = v26 -> zget_l R' [] kS11 = v27 ->
     zget_l R' [] kGP = zget_l Rb l kGP -> zget_l R' [] kTP = zget_l Rb l kTP ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) v1 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd Rb l) M MD) T.
Proof using C zc ret pb p wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hh LSP LA6 HSL Hev Hv1 K.
  remember (zget_l Rb l kGP) as vgp' eqn:EG. remember (zget_l Rb l kTP) as vtp' eqn:ET. symmetry in EG, ET.
  pose proof C as C'. open_itc C'. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  unfold slots_t in HSL. dand HSL as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
  zrebase.
  zstep Rfd.                                       (* [comment removed for export] *)
  do 13 (zstep Rfd).                               (* [comment removed for export] *)
  zstep Rfd.                                       (* [comment removed for export] *)
  zret Rfd.                                        (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  all: zreg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma setbits_t : forall Rb l M MD T rv,
  m_halted MD = None -> pregs3_t Rb l -> zget_l Rb l kA4 = pb -> zget_l Rb l kA7 = rv -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  (forall R' M', pregs3_t R' [] -> zget_l R' [] kA6 = 0 -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' pb (pb + 4) 0 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' pb rv ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101320 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T rv Hh HP LA4 LA7 Wp K.
  pose proof C as C'. open_itc C'. unfold pregs3_t in HP. dand HP as (LSP & LGP & LTP). zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15. unfold ZSEP in Hpb.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M pb (pb + 4) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X pb (pb + 4) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.                                       (* [comment removed for export] *)
  zstep Rfd.                                       (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try kauto_t. all: try close_pregs3_t. all: exact HAG.
Qed.

Lemma it_room_ge_t : 128 <= it_room ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma break_tail_t : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kT1 = 256 * (t_len st - t_drop st) ->
  CM M -> SM st M -> SP st ->
  0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st ->
  (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
  (forall R' M', pregs3_t R' [] -> zget_l R' [] kA6 = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsT p pb) ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444
       (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                 else t_tbl st)) ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 160) (p + 1384 + 4 * (nx + t_used st)) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' pb rt ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 808) 288 (arr_get work1Ar) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101212 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LT1 HM HSM HP Hhb Hused Hhuff Hfit K.
  pose proof C as C'. open_itc C'. open_cmem_t HM. open_smem_t HSM. open_spure HP. zkeys. xaddr_t.
  clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15 LOWR DROPR.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C192') as RTF. pose proof it_room_ge_t as HRG.
  (* [comment removed for export] *)
  assert (J20 : forall RJ MJ, pregs3_t RJ [] -> zget_l RJ [] kA3 = p + 160 -> zget_l RJ [] kA4 = pb -> zget_l RJ [] kA7 = rt ->
            zget_l RJ [] kT5 = t_used st ->
            mpost (run_segments R_segs rc_inp rc_sp rc_mb) M MJ (p + 1384) (p + 7160) 0 0 ->
            mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 1384) 1444
              (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                        else t_tbl st)) ->
            mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MJ p 7176 ->
            mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 808) 288 (arr_get work1Ar) ->
            mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 160) (p + 1384 + 4 * nx) ->
            realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101268 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JA3 JA4 JA7 JT4 HPO HtblJ WfJ WpJ HlensJ HworkJ HnextJ.
    clear Hcnt Htbl Wf Wp Hlens Hwork Hnext Hsl8 Hsl16 Hsl24 Hsl32 Hext Hbase. unfold pregs3_t in HPJ. dand HPJ as (LSP & LGP & LTP). zkeys.
    pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 160) (p + 168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
    assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) MJ X (p + 160) (p + 168) 0 0) MJ) by (apply mpost_refl).
    zrebase.
    zstep Rfd.                                         (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    zstep Rfd. zsetreg (4 * t_used st) ltac:(symmetry; apply zext32_x4; lia).   (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    zbr Rfd false.                                     (* [comment removed for export] *)
    zstep Rfd. zstep Rfd. zstep Rfd.                   (* [comment removed for export] *)
    zsetreg 1 ltac:(rewrite !Z.mod_small by lia; destruct (Z.ltb_spec 0 (p + 1384 + 4 * nx)); [|lia];
                    destruct (Z.ltb_spec (4 * t_used st + (p + 1384 + 4 * nx)) 1); [lia|]; reflexivity).
    zbr Rfd false.                                     (* [comment removed for export] *)
    zstep Rfd. zsetreg (t_used st) ltac:(symmetry; apply zext32_id; lia).        (* [comment removed for export] *)
    zstep Rfd. zsetreg (4 * t_used st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
    zstep Rfd. zsetreg (p + 1384 + 4 * (nx + t_used st)) ltac:(lia).            (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_t Rx [] Mx MD T rt Hh) end.
    all: try kauto_t. all: try close_pregs3_t.
    intros R' M' HP' LA6 HPO2 Hbits'.
    destruct HPO2 as [HA2 HW2].
    eapply K; try eassumption.
    - pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M M MJ (rsT p pb) _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (rsT p pb)) HPO ltac:(left; cbn; left; lia) ltac:(right; lia)) as F1.
      pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M MJ _ (rsT p pb) _ _ _ _ F1 HAG ltac:(left; cbn; right; left; lia) ltac:(right; lia)) as F2.
      exact (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M _ M' (rsT p pb) _ _ _ _ F2 (conj HA2 HW2) ltac:(left; cbn; right; right; left; unfold ZSEP in Hpb; lia) ltac:(right; lia)).
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_u64_magree; [exact HA2 | eassumption | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    - apply HW2. assumption.
    - apply HW2. assumption.
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia]. }
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  open_cregs_t HC. open_sregs_t HS. zkeys. zrebase.
  destruct (Z.eq_dec (t_huff st) 0) as [H0|HN0].
  - zbr Rfd true.                                      (* [comment removed for export] *)
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J20 Rx M) end.
    all: try kauto_t. all: try close_pregs3_t. all: try assumption.
    rewrite H0. cbn [Z.eqb negb]. exact Htbl.
  - zbr Rfd false.
    specialize (Hfit HN0).
    destruct (arr4_hole (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
    zbr Rfd false.                                     (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    zstep Rfd. zsetreg (4 * t_huff st) ltac:(symmetry; apply zext32_x4; lia).   (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    zbr Rfd false.                                     (* [comment removed for export] *)
    zbr Rfd false.                                     (* [comment removed for export] *)
    zstep Rfd. zsetreg (t_huff st) ltac:(symmetry; apply zext32_id; lia).       (* [comment removed for export] *)
    zstep Rfd. zsetreg (4 * t_huff st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).   (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    zstep Rfd. zsetreg (64 + 256 * (t_len st - t_drop st))
      ltac:(replace (256 * (t_len st - t_drop st)) with (Z.shiftl (t_len st - t_drop st) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
            rewrite Z.lor_comm, lor_shiftl_add by (try (change (2 ^ 8) with 256); lia); rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).   (* [comment removed for export] *)
    zstep Rfd. zsetreg 0 ltac:(symmetry; rewrite srli_small by lia; apply Z.div_small; change (2 ^ 16) with 65536; lia).   (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    zstep Rfd.                                         (* [comment removed for export] *)
    match goal with
    | Hlo : mem_u16 _ ?Mc _ (64 + 256 * (t_len st - t_drop st)), Hhi : mem_u16 _ _ _ 0 |- _ =>
      pose proof (entry_write2_t Mc (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) _ 0 _ _ HT1 HT2 Hlo Hhi
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
      clear Hlo Hhi HT1 HT2
    end.
    rewrite (Z.mod_small (64 + 256 * (t_len st - t_drop st))) in Htbl by lia.
    replace (64 + 256 * (t_len st - t_drop st) + 65536 * 0) with (code_pack 64 (t_len st - t_drop st) 0) in Htbl by (rewrite code_pack_small by lia; lia).
    apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J20 Rx Mx) end.
    all: try kauto_t. all: try close_pregs3_t. all: try assumption.
    destruct (Z.eqb_spec (t_huff st) 0); [lia|]. cbn [negb]. exact Htbl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma max0_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> mx = 0 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf ->
  (forall R' M', pregs3_t R' [] -> zget_l R' [] kA6 = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsT p pb) ->
     mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0))) ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 160) (p + 1384 + 4 * (nx + 2)) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' pb 1 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 808) 288 wf ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101424 (zupd Rb l) M MD) T.
Proof using C zc ret bits.
  intros Rb l M MD T Hh HP Hmx0 Wp Htbl Hnext Wf Hlens Hwork K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear Hprom HtyC HtyD Hlf Hwf Hlens15.
  pose proof it_room_ge_t as HRG.
  assert (Htbl' : mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (tblA cf))).
  { eapply mem_arr_ext; [exact Htbl|]. intros j _. symmetry. apply tblA_get. }
  clear Htbl.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (rsT p pb) ltac:(cbn; unfold ZSEP in Hpb; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (rsT p pb)) M) by (apply mpostL_refl).
  destruct (arr4_hole (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 (arr_get (tblA cf)) nx Htbl' ltac:(lia)) as [HT1 HT2]. clear Htbl'.
  zrebase.
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zbr Rfd false.                                       (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2_t Mc (p + 1384) 1444 (arr_get (tblA cf)) nx 320 0 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  change (320 mod 65536 + 65536 * 0) with 320 in Htbl.
  apply mem_arr_arr_set in Htbl; [| unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  destruct (arr4_hole (run_segments R_segs rc_inp rc_sp rc_mb) _ (p + 1384) 1444 _ (nx + 1) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zbr Rfd false.                                       (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2_t Mc (p + 1384) 1444 _ (nx + 1) 320 0 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  change (320 mod 65536 + 65536 * 0) with 320 in Htbl.
  apply mem_arr_arr_set in Htbl; [| rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  zstep Rfd.                                           (* [comment removed for export] *)
  zstep Rfd.                                           (* [comment removed for export] *)
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_t Rx [] Mx MD T 1 Hh) end.
  all: try kauto_t. all: try close_pregs3_t.
  intros R' M' HP' LA6 HPO2 Hbits'. destruct HPO2 as [HA2 HW2].
  eapply K; try eassumption.
  - exact (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M _ M' (rsT p pb) _ _ _ _ HAG (conj HA2 HW2) ltac:(left; cbn; right; right; left; unfold ZSEP in Hpb; lia) ltac:(right; lia)).
  - eapply mem_arr_magree; [exact HA2 | | unfold ZSEP in Hpb; lia | lia].
    change (code_pack 64 1 0) with 320. exact Htbl.
  - eapply mem_u64_magree; [exact HA2 | | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    match goal with H : mem_u64 _ _ (p + 160) ?v |- _ => replace (p + 1384 + 4 * (nx + 2)) with v by lia; exact H end.
  - apply HW2. assumption.
  - apply HW2. assumption.
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
Qed.
End U8IT6.
End T_It6.

Module T_It7.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It5 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It6.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.Base OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I8U.T_It2 T_It3 T_It4 T_It5 T_It6.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section U8IT7.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

(* [comment removed for export] *)
Definition FP : list (Z * Z) := [(sp - 208, 208); (p + 160, 8); (pb, 4); (p + 808, 576); (p + 1384, 5776)].
Definition FPS : list (Z * Z) := [(sp + -208, 104); (p + 160, 8); (pb, 4); (p + 808, 576); (p + 1384, 5776)].

(* [comment removed for export] *)
Definition pf (M : mem) : Prop :=
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 160) (p + 1384 + 4 * nx) /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M pb bits /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67170 31 (arr_get lbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67232 31 (arr_get lext_a) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67294 32 (arr_get dbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M 67358 32 (arr_get dext_a).
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  dand H as (a & b & c & d & e & f & g & h & i & j).

Lemma pf_frame : forall M M' lo hi, pf M -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' lo hi 0 0 -> zc <= lo -> pf M'.   (* [comment removed for export] *)
Proof using C ret sp codes lens_ofs ty.
  intros M M' lo hi HP [HA HW] Hlo. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb. open_pf HP. unfold pf. split_conj.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Htabl | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u32_magree; [exact HA | exact Hbcell | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hlb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hle | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hdb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hde | lia_std | lia_std].
Qed.

(* [comment removed for export] *)
Lemma slots_fps : forall M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  slots_t sp M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' FPS ->
  slots_t sp M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 HS [HA HW]. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb.
  unfold slots_t in *. destr_conj HS. split_conj.
  all: eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | rewrite two64_eq; lia_std | cbn; lia_std].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma acc2 : forall M0 M M' a1 b1 a2 b2,
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPS) M -> mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' a1 b1 a2 b2 ->
  in_some a1 (b1 - a1) FPS \/ b1 <= a1 -> in_some a2 (b2 - a2) FPS \/ b2 <= a2 ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPS) M'.
Proof using. intros. eapply framed_mpostL_trans2; eassumption. Qed.
Lemma accL : forall M0 M M', framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPS) M -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsL p sp) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.
Lemma accT : forall M0 M M', framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPS) M -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (rsT p pb) ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.

(* [comment removed for export] *)
Lemma safe_sort : mx <> 0 -> itm_reject ty mx (it_left_check cntAr) = false ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true /\
  (it_not_enough ty (itm_used rt) = false -> it_loop_ok (Z.to_nat (codes + 1)) X 288 320 1444 st0 = true).
Proof using C zc ret sp pb p.
  intros Hmx Hrj.
  pose proof (it_safe_sort ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ C)) as S.
  cbv zeta in S. unfold mxA, cntA, rootA, mnA, mxA, cntA, offsA, work1A, offsA, cntA in *.
  specialize (S Hmx Hrj). destruct S as [S1 S2].
  unfold workA, lensA, tblA in S1, S2 |- *. rewrite !arr_len_init in S1, S2. cbv [N_WORK N_LENS N_CODES] in S1, S2 |- *.
  split; [exact S1 | intros Hne; exact (proj2 (proj2 (S2 Hne)))].
Qed.

Lemma fin_fp : forall M M1 M', mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M1 (sp + -208) sp 0 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 M' FPS -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' FP.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M1 M' HP [HA HW]. pose proof C as C'. open_itc C'.
  pose proof (framed_mpostL_trans2 (run_segments R_segs rc_inp rc_sp rc_mb) M M M1 FP _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M FP) HP ltac:(left; cbn; left; lia_std) ltac:(right; lia_std)) as [A1 W1].
  split; [| intros a n Hw; apply HW; apply W1; exact Hw].
  intros x Hx. rewrite (HA x); [apply A1; exact Hx|]. cbn in Hx |- *. lia_std.
Qed.

Lemma cA_zero : codes = 0 -> forall j, arr_get cntAr j = 0.
Proof using. intros Hc j. rewrite cntA_eq, Hc. unfold cntK. rewrite itm_count_k_0 by lia_std. apply it_zero_count_spec. Qed.

Lemma tbl_max0_range : forall j, 0 <= j < 1444 ->
  0 <= arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0)) j < 4294967296.
Proof using C zc ret sp pb p wf bits codes lens_ofs lf ty.
  intros j Hj. pose proof C as C'. open_itc C'.
  rewrite !arr_get_set. destruct (_ && _); [apply code_pack_range|]. destruct (_ && _); [apply code_pack_range|].
  rewrite tblA_get. apply Hcf. exact Hj.
Qed.
Lemma tbl_brk_range : forall st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 ->
  0 <= arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st) j < 4294967296.
Proof using.
  intros st H j Hj. destruct (negb _); [|apply H; exact Hj]. rewrite arr_get_set. destruct (_ && _); [apply code_pack_range | apply H; exact Hj].
Qed.
Lemma tblA_range : forall j, 0 <= j < 1444 -> 0 <= arr_get (tblA cf) j < 4294967296.
Proof using C zc ret sp pb p wf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite tblA_get. apply Hcf. exact Hj. Qed.
Lemma workA_range : forall j, 0 <= j < 288 -> 0 <= arr_get (workA wf) j < 65536.
Proof using C zc ret sp pb p cf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite workA_get. apply Hwf. exact Hj. Qed.
End U8IT7.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  dand H as (a & b & c & d & e & f & g & h & i & j).

Ltac zkeys_all := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in *.

Theorem itable_t {RCa1 : RunCtx}  : itable_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_ITABLE_T 208.
Proof.
  unfold itable_spec_at, A_ITABLE_T.
  intros Rb l M MD T ty p lens_ofs codes nx bits pb sp ret zc lf cf wf.
  intros Hh LA0 LA1 LA2 LA3 LA4 LA5 LSP LRA Hret Hret2 Hpb Hpal Hp0 Hpceil Hsp Hzrom Hsp2 Hspal Hprom
         Wf0 Wp0 Hlens0 Htab0 Hwork0 Hnext0 Hbits0 Hlb0 Hle0 Hdb0 Hde0 Rlf Rcf Rwf
         Hofs Hofs2 Hc0 Hc288 Hl15 HtyC HtyD Hb1 Hb15 Hnx Hroom K.
  cbv [o_lens o_next o_work o_codes N_LENS N_CODES N_WORK STATE_SIZE LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR
       o_lenbits o_distbits ROM_LO_ALL it_fp] in *.
  set (vgp := zget_l Rb l kGP). set (vtp := zget_l Rb l kTP).
  assert (C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc).
  { constructor; cbv [N_LENS N_CODES N_WORK STATE_SIZE o_lenbits o_distbits ROM_LO_ALL DEXT_ADDR]; try assumption; try lia_std. }
  pose proof (C192 _ _ _ _ _ _ _ _ _ _ _ _ _ C) as C192v.
  assert (PF0 : pf lf nx bits cf wf p pb M) by (unfold pf; split_conj; assumption).
  (* [comment removed for export] *)
  assert (FIN : forall R' M' rv (T' W' : arr) tab' b',
    resA ty lf lens_ofs codes nx bits cf wf = (rv, T', tab', b', W') ->
    zget_l R' [] kSP = sp + -208 -> zget_l R' [] kGP = vgp -> zget_l R' [] kTP = vtp -> zget_l R' [] kA6 = rv ->
    slots_t sp M' ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9)
          (zget_l Rb l kS10) (zget_l Rb l kS11) ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (FP p pb sp) ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 (arr_get T') -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 808) 288 (arr_get W') ->
    (forall i, 0 <= i < 1444 -> 0 <= arr_get T' i < 4294967296) -> (forall i, 0 <= i < 288 -> 0 <= arr_get W' i < 65536) ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 160) (p + 1384 + 4 * tab') -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' pb b' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101328 (zupd R' []) M' MD) T).
  { intros R' M' rv T' W' tab' b' ER LSP' LGP' LTP' LA6' HSL HPL Hlens' Htab' Hwork' RT RW Hnext' Hbits'.
    eapply (epilogue_t ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C R' [] M' MD T rv ret); try eassumption.
    intros R'' FA0 FSP FRA FS0 FS1 FS2 FS3 FS4 FS5 FS6 FS7 FS8 FS9 FS10 FS11 FGP FTP.
    assert (RES : it_ret (resA ty lf lens_ofs codes nx bits cf wf) = rv /\ it_tbl (resA ty lf lens_ofs codes nx bits cf wf) = T' /\
                  it_table (resA ty lf lens_ofs codes nx bits cf wf) = tab' /\ it_bits (resA ty lf lens_ofs codes nx bits cf wf) = b' /\
                  it_work (resA ty lf lens_ofs codes nx bits cf wf) = W').
    { rewrite ER. repeat split; reflexivity. }
    unfold resA, lensA, tblA, workA in RES. cbv [N_LENS N_CODES N_WORK] in RES. dand RES as (E1 & E2 & E3 & E4 & E5).
    assert (RV3 : rv = 0 \/ rv = 1 \/ rv = -1).
    { pose proof (res_phases ty lf lens_ofs codes nx bits cf wf) as PH. rewrite ER in PH.
      destruct (mxA lf lens_ofs codes =? 0); [injection PH; intros; lia_std|].
      destruct (itm_reject _ _ _); [injection PH; intros; lia_std|].
      destruct (it_not_enough _ _); [injection PH; intros; lia_std|].
      destruct (it_loop _ _ _); injection PH; intros; lia_std. }
    eapply (K R'' M' (arr_get T') (arr_get W')); cbv zeta; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
    all: try (intros; reflexivity).
    unfold kept_eq. cbv [zget_l alookup] in FSP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FGP, FTP.
    rewrite FSP, FGP, FTP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11. subst vgp vtp.
    repeat split; first [reflexivity | symmetry; assumption | assumption]. }
  pose proof (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as SAFE.
  (* [comment removed for export] *)
  eapply (it_prologue_t Rb l M MD T sp ret vgp vtp (zget_l Rb l kS0) (zget_l Rb l kS1) (cty ty) (p + 168 + 2 * lens_ofs) codes (p + 160) pb (p + 808)
            (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4) (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7)
            (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11) Hh); try assumption; try reflexivity; try lia.
  intros R1 M1 QSP QGP QTP QA0 QA1 QA2 QA3 QA4 QA5 HPO1 Wf1 S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 Hcnt0.
  assert (HSL1 : slots_t sp M1 ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11))
    by (unfold slots_t; split_conj; assumption).
  clear S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27.
  pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M M1 _ _ PF0 HPO1 ltac:(lia)) as PF1.
  assert (HAGS1 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M1) by (apply mpostL_refl).
  assert (PR1 : pregs p lens_ofs codes pb sp vgp vtp (cty ty) R1 []) by (unfold pregs; split_conj; assumption).
  (* [comment removed for export] *)
  assert (KC : forall Mc, pf lf nx bits cf wf p pb Mc -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mc (sp - 208) 208 -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) Mc (sp + -136) 16 (arr_get (cntA lf lens_ofs codes)) ->
            framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) Mc ->
            T_It1.Kleft ty lf lens_ofs codes bits p pb sp vgp vtp Mc MD T /\ T_It1.Kmax0 ty lf lens_ofs codes p pb sp vgp vtp Mc MD T).
  { intros Mc PFc Wfc Hcntc HAGc. pose proof PFc as PFc'. unfold pf in PFc'.
    dand PFc' as (Wpc & Hlens1 & Htabl0 & Hwork1 & Hnext1 & Hbcell0 & Hlb1 & Hle1 & Hdb1 & Hde1). split.
    - (* [comment removed for export] *)
      apply (left_t ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Hcntc).
      + (* [comment removed for export] *)
        unfold T_It2.Kneg. intros R' HP' LA6 Hrj Hmx1. open_pregs HP'.
        eapply (FIN R' Mc (-1) (tblA cf) (workA wf) nx bits); try eassumption.
        * rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj. reflexivity.
        * eapply slots_fps; [exact C | exact HSL1 | exact HAGc].
        * eapply fin_fp; [exact C | exact HPO1 | exact HAGc].
        * eapply mem_arr_ext; [exact Htabl0|]. intros; symmetry; apply tblA_get.
        * eapply mem_arr_ext; [exact Hwork1|]. intros; symmetry; apply workA_get.
        * apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
        * apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      + (* [comment removed for export] *)
        apply (offs_t ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Wfc).
        intros R3 M3 HP3 LT0 LT1 LA7 LT2x HPO3 Hoffs Hmx1 Hrj.
        assert (Hmx0 : mxA lf lens_ofs codes <> 0) by lia.
        destruct (safe_sort _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx0 Hrj) as [SOK LOOPOK].
        pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C Mc M3 _ _ PFc HPO3 ltac:(lia)) as PF3.
        dand PF3 as (Wp3 & Hlens3 & Htab3 & Hwork3 & Hnext3 & Hbits3 & Hlb3 & Hle3 & Hdb3 & Hde3).
        assert (HAG3 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M3) by (eapply acc2; [exact HAGc | exact HPO3 | left; cbn; left; lia | right; lia]).
        assert (Wf3 : mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M3 (sp - 208) 208) by (destruct HPO3 as [_ HW]; apply HW; exact Wfc).
        eapply (sort_phase_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M3 MD T Hh HP3 LT0 LT1 LA7 LT2x Hmx1 SOK Wf3 Wp3 Hlens3 Hoffs Hwork3).
        intros R4 M4 HP4 LT0' LT1' LA7' HPO4 Wf4 Wp4 Hlens4 Hwork4.
        destruct HPO4 as [HA4 HW4]. unfold ZSEP in Hprom, Hpb.
        assert (HAG4 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M4) by (eapply acc2; [exact HAG3 | exact (conj HA4 HW4) | left; cbn; left; lia | left; cbn; right; right; right; left; lia]).
        assert (Htab4 : mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M4 (p + 1384) 1444 cf) by (eapply mem_arr_magree; [exact HA4 | exact Htab3 | lia | lia]).
        assert (Hnext4 : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M4 (p + 160) (p + 1384 + 4 * nx)) by (eapply mem_u64_magree; [exact HA4 | exact Hnext3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hbits4 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M4 pb bits) by (eapply mem_u32_magree; [exact HA4 | exact Hbits3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hlb4 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M4 67170 31 (arr_get lbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hlb3 | lia | lia]).
        assert (Hle4 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M4 67232 31 (arr_get lext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hle3 | lia | lia]).
        assert (Hdb4 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M4 67294 32 (arr_get dbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hdb3 | lia | lia]).
        assert (Hde4 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M4 67358 32 (arr_get dext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hde3 | lia | lia]).
        assert (Hcnt4 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M4 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
        { eapply mem_arr_magree; [exact HA4 | | lia | lia]. destruct HPO3 as [HA3 _]. eapply mem_arr_magree; [exact HA3 | exact Hcntc | lia | lia]. }
        clear HA4 HW4 Htab3 Hnext3 Hbits3 Hlb3 Hle3 Hdb3 Hde3 Hwork3 Hlens3 Wp3 Htabl0 Hnext1 Hbcell0 Hlb1 Hle1 Hdb1 Hde1 Hwork1 Hlens1 Wpc.
        eapply (switch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R4 [] M4 MD T Hh HP4 LT0' LT1' LA7' Hmx1 Wf4 Wp4 Hlens4 Hwork4 Hcnt4 Htab4 Hnext4 Hlb4 Hle4 Hdb4 Hde4).
        * (* [comment removed for export] *)
          intros R5 M5 HC5 HS5 L51 L52 HPO5 HM5 HSM5 HSP5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          assert (Hbits5 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M5 pb bits).
          { destruct HPO5 as [HA5 _]. eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia]. }
          specialize (LOOPOK Hne).
          assert (PHc : 0 <= codes <= 288) by lia.
          assert (PHl : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15).
          { intros s Hs. rewrite lensA_get. pose proof (Rlf (lens_ofs + s) ltac:(lia)). pose proof (Hl15 s Hs). lia. }
          assert (PHt : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (lensA lf) (lens_ofs + s) <= 7).
          { intros E. destruct (HtyC E) as (A & B & D). repeat split; try assumption. intros s Hs. rewrite lensA_get. apply D. exact Hs. }
          assert (PHb : 1 <= bits <= 15) by lia.
          assert (PHI1 : forall st, OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3.PIc_mod.PIc ty lf lens_ofs codes nx bits st -> ty = CODES -> tr_w st < it_match ty).
          { intros st0 HPIc Ety. unfold tr_w. assert (EM : it_match ty = 20) by (rewrite Ety; reflexivity). rewrite EM. exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3.PIc_mod.pic_w ty lf lens_ofs codes nx bits PHc PHl PHt PHb Hmx1 Hrj st0 HPIc Ety). }
          eapply (main_loop_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3.PIc_mod.PIc ty lf lens_ofs codes nx bits) PHI1
                    (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3.PIc_mod.pic_step ty lf lens_ofs codes nx bits PHc PHl PHt PHb Hmx1 Hrj)
                    (Z.to_nat (codes + 1)) _ R5 [] M5 M5 MD T LOOPOK Hmx1
                    (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_It3.PIc_mod.pic_init ty lf lens_ofs codes nx bits cf wf PHc PHl PHt PHb Hmx1 Hrj Hne)
                    Hh HC5 HS5 L51 L52 HM5 HSM5 HSP5 (mpostL_refl _ _ _)).
          -- (* [comment removed for export] *)
             intros st' R6 M6 HL HC6 HS6 L8 HPL6 HM6 HSM6 HSP6 Hfit B1 B2 B3.
             assert (HAG6 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             eapply (break_tail_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C st' R6 [] M6 MD T Hh HC6 HS6 L8 HM6 HSM6 HSP6 B1 B2 B3 Hfit).
             intros R7 M7 HP7 LA6 HPT7 Htbl7 Hnext7 Hbits7 Wf7 Wp7 Hlens7 Hwork7.
             assert (HAG7 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M7) by (eapply accT; [exact HAG6 | exact HPT7]).
             unfold pregs3_t in HP7. dand HP7 as (P1 & P2 & P3).
             pose proof HSP6 as HSP6'. unfold spure in HSP6'. dand HSP6' as (WK6 & _ & _ & _ & _ & _ & HTR6 & _ & _).
             eapply (FIN R7 M7 0 _ (t_work st') (nx + t_used st') (rootA lf lens_ofs codes bits)); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG7].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG7].
             ++ rewrite WK6. exact Hwork7.
             ++ apply tbl_brk_range. exact HTR6.
             ++ rewrite WK6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192v).
          -- (* [comment removed for export] *)
             intros st' R6 M6 HL HC6 LA6 HPL6 HM6 HSM6 HW6 HTR6.
             assert (HAG6 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             unfold cregs_t in HC6. dand HC6 as (HP6 & _). unfold pregs8 in HP6. dand HP6 as (P1 & P2 & P3 & _).
             unfold cmem_t in HM6. dand HM6 as (Wf6 & Wp6 & Hlens6 & Hwork6 & Hnext6 & _).
             unfold smem_t in HSM6. dand HSM6 as (Hcnt6 & Htbl6).
             assert (Hbits6 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M6 pb bits).
             { destruct HPL6 as [HA6 _]. eapply mem_u32_magreeL; [exact HA6 | exact Hbits5 | lia | rewrite two64_eq; lia | cbn; lia]. }
             eapply (FIN R6 M6 1 (t_tbl st') (t_work st') nx bits); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG6].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG6].
             ++ rewrite HW6. exact Hwork6.
             ++ rewrite HW6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192v).
        * (* [comment removed for export] *)
          intros R5 M5 HP5 LA6 HPO5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          destruct HPO5 as [HA5 HW5].
          unfold pregs8 in HP5. dand HP5 as (P1 & P2 & P3 & _).
          eapply (FIN R5 M5 1 (tblA cf) (work1A lf lens_ofs codes wf) nx bits); try eassumption.
          -- rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne. reflexivity.
          -- eapply slots_fps; [exact C | exact HSL1 | exact HAG5].
          -- eapply fin_fp; [exact C | exact HPO1 | exact HAG5].
          -- eapply mem_arr_magree; [exact HA5 | exact Hlens4 | lia | lia].
          -- eapply mem_arr_magree; [exact HA5 | | lia | lia]. eapply mem_arr_ext; [exact Htab4|]. intros; symmetry; apply tblA_get.
          -- eapply mem_arr_magree; [exact HA5 | exact Hwork4 | lia | lia].
          -- apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          -- apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C192v).
          -- eapply mem_u64_magree; [exact HA5 | exact Hnext4 | lia | rewrite two64_eq; lia | lia | lia].
          -- eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia].
    - (* [comment removed for export] *)
      unfold T_It1.Kmax0. intros R' HP' Hmx0.
      eapply (max0_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R' [] Mc MD T Hh HP' Hmx0 Wpc Htabl0 Hnext1 Wfc Hlens1 Hwork1).
      intros R2 M2 HP2 LA6 HPT2 Htbl2 Hnext2 Hbits2 Wf2 Wp2 Hlens2 Hwork2.
      assert (HAG2 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M2) by (eapply accT; [exact HAGc | exact HPT2]).
      unfold pregs3_t in HP2. dand HP2 as (P1 & P2 & P3).
      eapply (FIN R2 M2 0 _ (workA wf) (nx + 2) 1); try eassumption.
      + rewrite res_phases. rewrite Hmx0. reflexivity.
      + eapply slots_fps; [exact C | exact HSL1 | exact HAG2].
      + eapply fin_fp; [exact C | exact HPO1 | exact HAG2].
      + eapply mem_arr_ext; [exact Hwork2|]. intros; symmetry; apply workA_get.
      + apply (tbl_max0_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      + apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C). }
  (* [comment removed for export] *)
  pose proof PF1 as PF1'. unfold pf in PF1'. dand PF1' as (Wp1 & HlensM1 & HtabM1 & HworkM1 & HnextM1 & HbitsM1 & _).
  destruct (Z.eq_dec codes 0) as [Cz|Cnz].
  - (* [comment removed for export] *)
    assert (HcntA : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M1 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
    { eapply mem_arr_ext; [exact Hcnt0|]. intros; symmetry; apply cA_zero; exact Cz. }
    destruct (KC M1 PF1 Wf1 HcntA HAGS1) as [_ KM0].
    eapply (count_phase0_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T _ Cz Hh PR1 eq_refl Hcnt0 HbitsM1 KM0).
  - eapply (count_phase_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T ltac:(lia) Hh PR1 Wf1 HlensM1 Hcnt0).
    intros R2 M2 PR2 QA7 HPO2 Wf2 Hlens2 Hcnt2.
    pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M1 M2 _ _ PF1 HPO2 ltac:(lia)) as PF2.
    assert (HAG2 : framed (fun Xm => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M1 Xm (FPS p pb sp)) M2) by (eapply acc2; [exact HAGS1 | exact HPO2 | left; cbn; left; lia | right; lia]).
    destruct (KC M2 PF2 Wf2 Hcnt2 HAG2) as [KL KM0].
    pose proof PF2 as PF2'. unfold pf in PF2'. dand PF2' as (_ & _ & _ & _ & _ & HbitsM2 & _).
    eapply (max_entry_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R2 [] M2 MD T _ Hh PR2 QA7 Hcnt2 HbitsM2).
    + unfold T_It1.Kmax. intros R3 HP3 LA7 LT0 LT2 Hmx2.
      eapply (rootmin_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 LT0 LT2 Hmx2 Hcnt2 KL).
    + unfold T_It1.Klow. intros R3 HP3 LA7 LT2 HZ.
      eapply (maxlow_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 LT2 HZ Hcnt2 KL KM0).
Qed.



End T_It7.

