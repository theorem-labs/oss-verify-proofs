(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia AmLiaKD.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | am_lia_kd ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE8z z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition unreg_words : list (option (bv 32)) :=
  [
   Some W_59e40; Some W_59e44; Some W_59e48; Some W_59e4c; Some W_59e50; Some W_59e54; Some W_59e58; Some W_59e5c;
   Some W_59e60; Some W_59e64; Some W_59e68; Some W_59e6c; Some W_59e70; Some W_59e74; Some W_59e78; None;
   None; Some W_59e84; Some W_59e88; Some W_59e8c; Some W_59e90; None; Some W_59e98; Some W_59e9c;
   Some W_59ea0; None; Some W_59ea8; Some W_59eac; Some W_59eb0; Some W_59eb4; Some W_59eb8; Some W_59ebc;
   Some W_59ec0; Some W_59ec4; Some W_59ec8; Some W_59ecc; Some W_59ed0; Some W_59ed4; Some W_59ed8; Some W_59edc;
   Some W_59ee0; Some W_59ee4; Some W_59ee8; Some W_59eec; Some W_59ef0; Some W_59ef4; Some W_59ef8; Some W_59efc;
   Some W_59f00; Some W_59f04; Some W_59f08; Some W_59f0c; Some W_59f10; Some W_59f14; Some W_59f18; Some W_59f1c;
   Some W_59f20; Some W_59f24; Some W_59f28; Some W_59f2c; Some W_59f30; Some W_59f34; Some W_59f38; Some W_59f3c;
   Some W_59f40; Some W_59f44; Some W_59f48; Some W_59f4c; Some W_59f50; Some W_59f54; Some W_59f58; Some W_59f5c;
   Some W_59f60; Some W_59f64; Some W_59f68; Some W_59f6c; Some W_59f70; Some W_59f74; None; None;
   None; None; None; None; None; None; None; Some W_59f9c;
   None; Some W_59fa4; None; Some W_59fac; None; None; None; Some W_59fbc;
   Some W_59fc0; None; None; Some W_59fcc; Some W_59fd0; Some W_59fd4; Some W_59fd8; Some W_59fdc;
   Some W_59fe0; Some W_59fe4; Some W_59fe8; Some W_59fec; Some W_59ff0; Some W_59ff4; Some W_59ff8; Some W_59ffc;
   Some W_5a000; Some W_5a004; Some W_5a008; Some W_5a00c; Some W_5a010; Some W_5a014; Some W_5a018; Some W_5a01c;
   Some W_5a020; Some W_5a024; Some W_5a028; Some W_5a02c; Some W_5a030; Some W_5a034; Some W_5a038; Some W_5a03c;
   Some W_5a040; Some W_5a044; Some W_5a048; Some W_5a04c; Some W_5a050; Some W_5a054; Some W_5a058; Some W_5a05c;
   Some W_5a060; Some W_5a064; Some W_5a068; Some W_5a06c; Some W_5a070; Some W_5a074; Some W_5a078; Some W_5a07c;
   Some W_5a080; Some W_5a084; Some W_5a088; Some W_5a08c; Some W_5a090; Some W_5a094; Some W_5a098; Some W_5a09c;
   Some W_5a0a0; Some W_5a0a4; Some W_5a0a8; Some W_5a0ac; Some W_5a0b0; Some W_5a0b4; Some W_5a0b8; Some W_5a0bc;
   Some W_5a0c0; Some W_5a0c4; Some W_5a0c8; Some W_5a0cc; Some W_5a0d0; Some W_5a0d4; Some W_5a0d8; Some W_5a0dc;
   Some W_5a0e0; Some W_5a0e4; Some W_5a0e8; Some W_5a0ec; Some W_5a0f0; Some W_5a0f4; Some W_5a0f8; Some W_5a0fc;
   Some W_5a100; Some W_5a104; Some W_5a108; Some W_5a10c; Some W_5a110; Some W_5a114; Some W_5a118; Some W_5a11c;
   Some W_5a120; Some W_5a124; Some W_5a128; Some W_5a12c; Some W_5a130; Some W_5a134; Some W_5a138; Some W_5a13c;
   Some W_5a140; Some W_5a144; Some W_5a148; Some W_5a14c; Some W_5a150; Some W_5a154; Some W_5a158; Some W_5a15c;
   Some W_5a160; Some W_5a164; Some W_5a168; Some W_5a16c; Some W_5a170; Some W_5a174; Some W_5a178; Some W_5a17c;
   Some W_5a180; Some W_5a184; Some W_5a188; Some W_5a18c; Some W_5a190; Some W_5a194; Some W_5a198; Some W_5a19c;
   Some W_5a1a0; Some W_5a1a4; Some W_5a1a8; Some W_5a1ac; Some W_5a1b0; Some W_5a1b4; Some W_5a1b8; Some W_5a1bc;
   Some W_5a1c0; Some W_5a1c4; Some W_5a1c8; Some W_5a1cc; Some W_5a1d0; Some W_5a1d4; Some W_5a1d8; Some W_5a1dc;
   Some W_5a1e0; Some W_5a1e4; Some W_5a1e8; Some W_5a1ec; Some W_5a1f0; Some W_5a1f4; Some W_5a1f8; Some W_5a1fc;
   Some W_5a200; Some W_5a204; Some W_5a208; Some W_5a20c; Some W_5a210; Some W_5a214; Some W_5a218; Some W_5a21c;
   Some W_5a220; Some W_5a224; Some W_5a228; Some W_5a22c; None; Some W_5a234; Some W_5a238; Some W_5a23c;
   None; Some W_5a244; Some W_5a248; Some W_5a24c; Some W_5a250; Some W_5a254; Some W_5a258; Some W_5a25c;
   Some W_5a260; Some W_5a264; Some W_5a268; Some W_5a26c; Some W_5a270; Some W_5a274; Some W_5a278; Some W_5a27c;
   Some W_5a280; Some W_5a284; Some W_5a288; Some W_5a28c; Some W_5a290; Some W_5a294; Some W_5a298; Some W_5a29c;
   Some W_5a2a0; Some W_5a2a4; Some W_5a2a8; Some W_5a2ac; Some W_5a2b0; Some W_5a2b4; Some W_5a2b8; Some W_5a2bc;
   Some W_5a2c0; Some W_5a2c4; Some W_5a2c8; Some W_5a2cc; Some W_5a2d0; Some W_5a2d4; Some W_5a2d8; Some W_5a2dc;
   Some W_5a2e0; Some W_5a2e4; Some W_5a2e8; Some W_5a2ec; Some W_5a2f0; Some W_5a2f4; Some W_5a2f8; Some W_5a2fc;
   Some W_5a300; Some W_5a304; Some W_5a308; Some W_5a30c; Some W_5a310; Some W_5a314; Some W_5a318; Some W_5a31c;
   Some W_5a320; Some W_5a324; Some W_5a328; Some W_5a32c; Some W_5a330; Some W_5a334; Some W_5a338; Some W_5a33c;
   Some W_5a340; Some W_5a344; Some W_5a348; Some W_5a34c; Some W_5a350; None; None; None;
   None; Some W_5a364; Some W_5a368; Some W_5a36c; Some W_5a370; None; Some W_5a378; None;
   None; Some W_5a384; Some W_5a388; Some W_5a38c; Some W_5a390; None; None; None;
   None; Some W_5a3a4; Some W_5a3a8; Some W_5a3ac; Some W_5a3b0; None; None; None;
   None; Some W_5a3c4; Some W_5a3c8; Some W_5a3cc; Some W_5a3d0; None; None; None;
   None; Some W_5a3e4; Some W_5a3e8; Some W_5a3ec; Some W_5a3f0; Some W_5a3f4; None; Some W_5a3fc;
   Some W_5a400; Some W_5a404; Some W_5a408; Some W_5a40c; Some W_5a410; Some W_5a414; Some W_5a418; Some W_5a41c;
   Some W_5a420; Some W_5a424; Some W_5a428; Some W_5a42c; Some W_5a430; Some W_5a434; Some W_5a438; Some W_5a43c;
   Some W_5a440; Some W_5a444; Some W_5a448; Some W_5a44c; Some W_5a450; Some W_5a454; Some W_5a458; None;
   Some W_5a460; None; None; Some W_5a46c; Some W_5a470; Some W_5a474; Some W_5a478; Some W_5a47c;
   Some W_5a480; Some W_5a484; Some W_5a488; Some W_5a48c; Some W_5a490; Some W_5a494; Some W_5a498; Some W_5a49c;
   Some W_5a4a0; Some W_5a4a4; Some W_5a4a8; Some W_5a4ac; Some W_5a4b0; Some W_5a4b4; Some W_5a4b8; Some W_5a4bc;
   Some W_5a4c0
  ]%list.

(* [comment removed for export] *)
Definition dtor_words : list (option (bv 32)) :=
  [Some W_bf020; Some W_bf024; None; None; None; None; None; None; None; Some W_bf044; Some W_bf048; Some W_bf04c]%list.

(* [comment removed for export] *)
Definition gapaddi (segs : list Segment) (base : word) (off1 off2 : Z) (rt rd : reg) (v : word) : Prop :=
  exists x : word,
    (forall regs mem rom,
        msteps segs (mkst regs (at_ base off1) mem rom) (mkst (regupd regs rt x) (at_ base (off1 + 4)) mem rom))
    /\ (forall regs mem rom,
           getr regs rt = x ->
           msteps segs (mkst regs (at_ base off2) mem rom) (mkst (regupd regs rd v) (at_ base (off2 + 4)) mem rom)).

(* [comment removed for export] *)
Definition gjal (segs : list Segment) (base : word) (off : Z) (tgt : word) : Prop :=
  forall regs mem rom,
    msteps segs (mkst regs (at_ base off) mem rom) (mkst (regupd regs 1 (at_ base (off + 4))) tgt mem rom).

(* [comment removed for export] *)
Definition cpm_call (segs : list Segment) (entry : word) (c_cpm : Z) : Prop :=
  forall regs mem rom (ra : word) (cpm : byte),
    rdn segs mem (Z_to_bv 64 c_cpm) 1 = Some [cpm] -> U cpm <> 0%Z -> ret_ok ra -> getr regs 1 = ra ->
    msteps segs (mkst regs entry mem rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) ra mem rom).

(* [comment removed for export] *)
Record unreg_tab : Type := UT {
  ut_dtor : word;            (* [comment removed for export] *)
  ut_base : word;            (* [comment removed for export] *)
  ut_pt : poison_tab;        (* [comment removed for export] *)
  ut_g_start : Z; ut_g_stop : Z;    (* [comment removed for export] *)
  ut_p_start : Z;
  ut_globs : list (Z * Z);   (* [comment removed for export] *)
  ut_p_flag : Z;             (* [comment removed for export] *)
  ut_g_aflags : Z; ut_p_aflags : Z;  (* [comment removed for export] *)
  ut_p_mu : Z;               (* [comment removed for export] *)
  ut_g_pgsz : Z;             (* [comment removed for export] *)
  ut_c_inited : Z;           (* [comment removed for export] *)
  ut_c_ro : Z;               (* [comment removed for export] *)
  ut_str : word }.           (* [comment removed for export] *)

Record unreg_tab_ok (segs : list Segment) (t : unreg_tab) : Prop := UTOK {
  uto_code : code_ato segs (ut_base t) 0 unreg_words;
  uto_dcode : code_ato segs (ut_dtor t) 0 dtor_words;
  uto_pt : poison_tab_ok segs (ut_pt t);
  uto_pt_base : pt_base (ut_pt t) = at_ (ut_base t) 88008;
  uto_ai : asan_inited_call segs (at_ (ut_base t) 110180) (ut_c_inited t);
  uto_cpm : cpm_call segs (at_ (ut_base t) 87988) (pt_c_cpm (ut_pt t));
  uto_g60 : gload2 segs (ut_base t) 60 11 25 (ut_g_aflags t);
  uto_g84 : gapaddi segs (ut_base t) 84 100 12 22 (Z_to_bv 64 (ut_p_mu t - 64));
  uto_g312 : gauipc_ld segs (ut_base t) 312 340 10 26 (pt_g_shoff (ut_pt t));
  uto_g316 : gauipc_ld segs (ut_base t) 316 344 11 10 (pt_g_midbeg (ut_pt t));
  uto_g320 : gauipc_ld segs (ut_base t) 320 352 12 10 (pt_g_midend (ut_pt t));
  uto_g324 : gauipc_ld segs (ut_base t) 324 360 13 10 (pt_g_hiend (ut_pt t));
  uto_g328 : gauipc_ld segs (ut_base t) 328 368 14 9 (pt_g_cfl (ut_pt t));
  uto_g332 : gauipc_ld segs (ut_base t) 332 372 15 23 (pt_g_rms (ut_pt t));
  uto_g336 : gauipc_ld segs (ut_base t) 336 376 16 10 (ut_g_pgsz t);
  uto_g388 : gaddr2 segs (ut_base t) 388 10 19 (ut_str t);
  uto_g1008 : gauipc_ld segs (ut_base t) 1008 1024 13 13 (ut_c_ro t);
  uto_d8 : gauipc_ld segs (ut_dtor t) 8 16 10 11 (ut_g_start t);
  uto_d12 : gauipc_ld segs (ut_dtor t) 12 20 12 12 (ut_g_stop t);
  uto_d24 : gaddr2 segs (ut_dtor t) 24 10 10 (Z_to_bv 64 (ut_p_flag t));
  uto_d32 : gjal segs (ut_dtor t) 32 (at_ (ut_base t) 1592);
  uto_base : (U (ut_base t) mod 2 = 0)%Z /\ (U (ut_base t) + 500000 < 2 ^ 64)%Z;
  uto_dbase : (U (ut_dtor t) mod 2 = 0)%Z /\ (U (ut_dtor t) + 48 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition zshad (b : Z) : Z := (b / 8 + 0x7fff8000)%Z.
(* [comment removed for export] *)
Fixpoint shz (M : word -> option byte) (l : list (Z * Z)) : word -> option byte :=
  match l with
  | [] => M
  | (b, s) :: l' => shz (wbytes M (Z_to_bv 64 (zshad b)) (repeat (cbyte (Z_to_bv 64 0)) (Z.to_nat (s / 8)))) l'
  end.

Lemma shz_app : forall l1 l2 M, shz M (l1 ++ l2) = shz (shz M l1) l2.
Proof using. induction l1 as [|[b s] l1 IH]; intros l2 M; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [shz app] in G in change_no_check G' end). apply IH. Qed.

Section UNREG.
  Variable segs : list Segment.
  Variables base dbase : word.
  Variable pt : poison_tab.
  Variables g_start g_stop p_start p_flag g_aflags p_aflags p_mu g_pgsz c_inited c_ro : Z.
  Variable globs : list (Z * Z).
  Variable v_str : word.
  #[local] Abbreviation g_shoff := (pt_g_shoff pt).
  #[local] Abbreviation p_shoff := (pt_p_shoff pt).
  #[local] Abbreviation g_midbeg := (pt_g_midbeg pt).
  #[local] Abbreviation p_midbeg := (pt_p_midbeg pt).
  #[local] Abbreviation g_midend := (pt_g_midend pt).
  #[local] Abbreviation p_midend := (pt_p_midend pt).
  #[local] Abbreviation g_hiend := (pt_g_hiend pt).
  #[local] Abbreviation p_hiend := (pt_p_hiend pt).
  #[local] Abbreviation g_rms := (pt_g_rms pt).
  #[local] Abbreviation p_rms := (pt_p_rms pt).
  #[local] Abbreviation g_cfl := (pt_g_cfl pt).
  #[local] Abbreviation p_cfl := (pt_p_cfl pt).
  #[local] Abbreviation c_cpm := (pt_c_cpm pt).
  #[local] Abbreviation mset := (pt_mset pt).
  Hypothesis HCODE : code_ato segs base 0 unreg_words.
  Hypothesis DCODE : code_ato segs dbase 0 dtor_words.
  Hypothesis PTOK : poison_tab_ok segs pt.
  Hypothesis PTB : pt_base pt = at_ base 88008.
  Hypothesis HAI : asan_inited_call segs (at_ base 110180) c_inited.
  Hypothesis HCPM : cpm_call segs (at_ base 87988) c_cpm.
  Hypothesis G60 : gload2 segs base 60 11 25 g_aflags.
  Hypothesis G84 : gapaddi segs base 84 100 12 22 (Z_to_bv 64 (p_mu - 64)).
  Hypothesis G312 : gauipc_ld segs base 312 340 10 26 g_shoff.
  Hypothesis G316 : gauipc_ld segs base 316 344 11 10 g_midbeg.
  Hypothesis G320 : gauipc_ld segs base 320 352 12 10 g_midend.
  Hypothesis G324 : gauipc_ld segs base 324 360 13 10 g_hiend.
  Hypothesis G328 : gauipc_ld segs base 328 368 14 9 g_cfl.
  Hypothesis G332 : gauipc_ld segs base 332 372 15 23 g_rms.
  Hypothesis G336 : gauipc_ld segs base 336 376 16 10 g_pgsz.
  Hypothesis G388 : gaddr2 segs base 388 10 19 v_str.
  Hypothesis G1008 : gauipc_ld segs base 1008 1024 13 13 c_ro.
  Hypothesis DG8 : gauipc_ld segs dbase 8 16 10 11 g_start.
  Hypothesis DG12 : gauipc_ld segs dbase 12 20 12 12 g_stop.
  Hypothesis DG24 : gaddr2 segs dbase 24 10 10 (Z_to_bv 64 p_flag).
  Hypothesis DJ32 : gjal segs dbase 32 (at_ base 1592).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 500000 < 2 ^ 64)%Z.
  Hypothesis Hdbase : (U dbase mod 2 = 0)%Z /\ (U dbase + 48 < 2 ^ 64)%Z.


  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_59e40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_59e44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_59e48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_59e4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_59e50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_59e54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_59e58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_59e5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_59e60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_59e64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_59e68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_59e6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_59e70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_59e74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_59e78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 14 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_59e84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_59e88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_59e8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_59e90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 20 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_59e98.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_59e9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_59ea0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 24 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_59ea8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_59eac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_59eb0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo116 : fetch_word segs (at_ base 116) = Some W_59eb4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 29 _ HCODE eq_refl). Qed.
  Lemma Fo120 : fetch_word segs (at_ base 120) = Some W_59eb8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_59ebc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo128 : fetch_word segs (at_ base 128) = Some W_59ec0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 32 _ HCODE eq_refl). Qed.
  Lemma Fo132 : fetch_word segs (at_ base 132) = Some W_59ec4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 33 _ HCODE eq_refl). Qed.
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_59ec8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_59ecc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 35 _ HCODE eq_refl). Qed.
  Lemma Fo144 : fetch_word segs (at_ base 144) = Some W_59ed0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 36 _ HCODE eq_refl). Qed.
  Lemma Fo148 : fetch_word segs (at_ base 148) = Some W_59ed4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 37 _ HCODE eq_refl). Qed.
  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_59ed8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_59edc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_59ee0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_59ee4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_59ee8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_59eec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_59ef0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_59ef4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_59ef8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 46 _ HCODE eq_refl). Qed.




























  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_59f6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_59f70.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 76 _ HCODE eq_refl). Qed.
  Lemma Fo308 : fetch_word segs (at_ base 308) = Some W_59f74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 77 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo348 : fetch_word segs (at_ base 348) = Some W_59f9c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 87 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_59fa4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 89 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma Fo364 : fetch_word segs (at_ base 364) = Some W_59fac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 91 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo380 : fetch_word segs (at_ base 380) = Some W_59fbc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 95 _ HCODE eq_refl). Qed.
  Lemma Fo384 : fetch_word segs (at_ base 384) = Some W_59fc0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 96 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo396 : fetch_word segs (at_ base 396) = Some W_59fcc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 99 _ HCODE eq_refl). Qed.
  Lemma Fo400 : fetch_word segs (at_ base 400) = Some W_59fd0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 100 _ HCODE eq_refl). Qed.
  Lemma Fo404 : fetch_word segs (at_ base 404) = Some W_59fd4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 101 _ HCODE eq_refl). Qed.
  Lemma Fo408 : fetch_word segs (at_ base 408) = Some W_59fd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 102 _ HCODE eq_refl). Qed.
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_59fdc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_59fe0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_59fe4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 105 _ HCODE eq_refl). Qed.
  Lemma Fo424 : fetch_word segs (at_ base 424) = Some W_59fe8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 106 _ HCODE eq_refl). Qed.
  Lemma Fo428 : fetch_word segs (at_ base 428) = Some W_59fec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 107 _ HCODE eq_refl). Qed.
  Lemma Fo432 : fetch_word segs (at_ base 432) = Some W_59ff0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 108 _ HCODE eq_refl). Qed.
  Lemma Fo436 : fetch_word segs (at_ base 436) = Some W_59ff4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 109 _ HCODE eq_refl). Qed.
  Lemma Fo440 : fetch_word segs (at_ base 440) = Some W_59ff8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 110 _ HCODE eq_refl). Qed.
  Lemma Fo444 : fetch_word segs (at_ base 444) = Some W_59ffc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 111 _ HCODE eq_refl). Qed.
  Lemma Fo448 : fetch_word segs (at_ base 448) = Some W_5a000.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 112 _ HCODE eq_refl). Qed.
  Lemma Fo452 : fetch_word segs (at_ base 452) = Some W_5a004.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 113 _ HCODE eq_refl). Qed.
  Lemma Fo456 : fetch_word segs (at_ base 456) = Some W_5a008.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 114 _ HCODE eq_refl). Qed.




  Lemma Fo476 : fetch_word segs (at_ base 476) = Some W_5a01c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 119 _ HCODE eq_refl). Qed.
  Lemma Fo480 : fetch_word segs (at_ base 480) = Some W_5a020.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 120 _ HCODE eq_refl). Qed.
  Lemma Fo484 : fetch_word segs (at_ base 484) = Some W_5a024.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 121 _ HCODE eq_refl). Qed.
  Lemma Fo488 : fetch_word segs (at_ base 488) = Some W_5a028.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 122 _ HCODE eq_refl). Qed.
  Lemma Fo492 : fetch_word segs (at_ base 492) = Some W_5a02c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 123 _ HCODE eq_refl). Qed.
  Lemma Fo496 : fetch_word segs (at_ base 496) = Some W_5a030.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 124 _ HCODE eq_refl). Qed.
  Lemma Fo500 : fetch_word segs (at_ base 500) = Some W_5a034.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 125 _ HCODE eq_refl). Qed.
  Lemma Fo504 : fetch_word segs (at_ base 504) = Some W_5a038.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 126 _ HCODE eq_refl). Qed.
























































  Lemma Fo732 : fetch_word segs (at_ base 732) = Some W_5a11c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 183 _ HCODE eq_refl). Qed.
  Lemma Fo736 : fetch_word segs (at_ base 736) = Some W_5a120.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 184 _ HCODE eq_refl). Qed.
  Lemma Fo740 : fetch_word segs (at_ base 740) = Some W_5a124.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 185 _ HCODE eq_refl). Qed.
  Lemma Fo744 : fetch_word segs (at_ base 744) = Some W_5a128.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 186 _ HCODE eq_refl). Qed.
  Lemma Fo748 : fetch_word segs (at_ base 748) = Some W_5a12c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 187 _ HCODE eq_refl). Qed.
  Lemma Fo752 : fetch_word segs (at_ base 752) = Some W_5a130.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 188 _ HCODE eq_refl). Qed.
  Lemma Fo756 : fetch_word segs (at_ base 756) = Some W_5a134.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 189 _ HCODE eq_refl). Qed.
  Lemma Fo760 : fetch_word segs (at_ base 760) = Some W_5a138.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 190 _ HCODE eq_refl). Qed.
  Lemma Fo764 : fetch_word segs (at_ base 764) = Some W_5a13c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 191 _ HCODE eq_refl). Qed.
  Lemma Fo768 : fetch_word segs (at_ base 768) = Some W_5a140.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 192 _ HCODE eq_refl). Qed.
  Lemma Fo772 : fetch_word segs (at_ base 772) = Some W_5a144.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 193 _ HCODE eq_refl). Qed.
  Lemma Fo776 : fetch_word segs (at_ base 776) = Some W_5a148.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 194 _ HCODE eq_refl). Qed.
  Lemma Fo780 : fetch_word segs (at_ base 780) = Some W_5a14c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 195 _ HCODE eq_refl). Qed.
  Lemma Fo784 : fetch_word segs (at_ base 784) = Some W_5a150.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 196 _ HCODE eq_refl). Qed.
  Lemma Fo788 : fetch_word segs (at_ base 788) = Some W_5a154.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 197 _ HCODE eq_refl). Qed.
  Lemma Fo792 : fetch_word segs (at_ base 792) = Some W_5a158.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 198 _ HCODE eq_refl). Qed.
  Lemma Fo796 : fetch_word segs (at_ base 796) = Some W_5a15c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 199 _ HCODE eq_refl). Qed.
  Lemma Fo800 : fetch_word segs (at_ base 800) = Some W_5a160.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 200 _ HCODE eq_refl). Qed.
  Lemma Fo804 : fetch_word segs (at_ base 804) = Some W_5a164.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 201 _ HCODE eq_refl). Qed.
  Lemma Fo808 : fetch_word segs (at_ base 808) = Some W_5a168.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 202 _ HCODE eq_refl). Qed.





































  Lemma Fo960 : fetch_word segs (at_ base 960) = Some W_5a200.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 240 _ HCODE eq_refl). Qed.
  Lemma Fo964 : fetch_word segs (at_ base 964) = Some W_5a204.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 241 _ HCODE eq_refl). Qed.
  Lemma Fo968 : fetch_word segs (at_ base 968) = Some W_5a208.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 242 _ HCODE eq_refl). Qed.
  Lemma Fo972 : fetch_word segs (at_ base 972) = Some W_5a20c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 243 _ HCODE eq_refl). Qed.
  Lemma Fo976 : fetch_word segs (at_ base 976) = Some W_5a210.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 244 _ HCODE eq_refl). Qed.
  Lemma Fo980 : fetch_word segs (at_ base 980) = Some W_5a214.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 245 _ HCODE eq_refl). Qed.
  Lemma Fo984 : fetch_word segs (at_ base 984) = Some W_5a218.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 246 _ HCODE eq_refl). Qed.
  Lemma Fo988 : fetch_word segs (at_ base 988) = Some W_5a21c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 247 _ HCODE eq_refl). Qed.
  Lemma Fo992 : fetch_word segs (at_ base 992) = Some W_5a220.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 248 _ HCODE eq_refl). Qed.
  Lemma Fo996 : fetch_word segs (at_ base 996) = Some W_5a224.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 249 _ HCODE eq_refl). Qed.
  Lemma Fo1000 : fetch_word segs (at_ base 1000) = Some W_5a228.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 250 _ HCODE eq_refl). Qed.
  Lemma Fo1004 : fetch_word segs (at_ base 1004) = Some W_5a22c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 251 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma Fo1012 : fetch_word segs (at_ base 1012) = Some W_5a234.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 253 _ HCODE eq_refl). Qed.
  Lemma Fo1016 : fetch_word segs (at_ base 1016) = Some W_5a238.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 254 _ HCODE eq_refl). Qed.
  Lemma Fo1020 : fetch_word segs (at_ base 1020) = Some W_5a23c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 255 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma Fo1028 : fetch_word segs (at_ base 1028) = Some W_5a244.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 257 _ HCODE eq_refl). Qed.
  Lemma Fo1032 : fetch_word segs (at_ base 1032) = Some W_5a248.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 258 _ HCODE eq_refl). Qed.
  Lemma Fo1036 : fetch_word segs (at_ base 1036) = Some W_5a24c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 259 _ HCODE eq_refl). Qed.
  Lemma Fo1040 : fetch_word segs (at_ base 1040) = Some W_5a250.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 260 _ HCODE eq_refl). Qed.
  Lemma Fo1044 : fetch_word segs (at_ base 1044) = Some W_5a254.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 261 _ HCODE eq_refl). Qed.
  Lemma Fo1048 : fetch_word segs (at_ base 1048) = Some W_5a258.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 262 _ HCODE eq_refl). Qed.
  Lemma Fo1052 : fetch_word segs (at_ base 1052) = Some W_5a25c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 263 _ HCODE eq_refl). Qed.
  Lemma Fo1056 : fetch_word segs (at_ base 1056) = Some W_5a260.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 264 _ HCODE eq_refl). Qed.
  Lemma Fo1060 : fetch_word segs (at_ base 1060) = Some W_5a264.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 265 _ HCODE eq_refl). Qed.
  Lemma Fo1064 : fetch_word segs (at_ base 1064) = Some W_5a268.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 266 _ HCODE eq_refl). Qed.

  Lemma Fo1072 : fetch_word segs (at_ base 1072) = Some W_5a270.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 268 _ HCODE eq_refl). Qed.
  Lemma Fo1076 : fetch_word segs (at_ base 1076) = Some W_5a274.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 269 _ HCODE eq_refl). Qed.
  Lemma Fo1080 : fetch_word segs (at_ base 1080) = Some W_5a278.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 270 _ HCODE eq_refl). Qed.
  Lemma Fo1084 : fetch_word segs (at_ base 1084) = Some W_5a27c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 271 _ HCODE eq_refl). Qed.
  Lemma Fo1088 : fetch_word segs (at_ base 1088) = Some W_5a280.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 272 _ HCODE eq_refl). Qed.








  Lemma Fo1124 : fetch_word segs (at_ base 1124) = Some W_5a2a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 281 _ HCODE eq_refl). Qed.
  Lemma Fo1128 : fetch_word segs (at_ base 1128) = Some W_5a2a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 282 _ HCODE eq_refl). Qed.
  Lemma Fo1132 : fetch_word segs (at_ base 1132) = Some W_5a2ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 283 _ HCODE eq_refl). Qed.
  Lemma Fo1136 : fetch_word segs (at_ base 1136) = Some W_5a2b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 284 _ HCODE eq_refl). Qed.
  Lemma Fo1140 : fetch_word segs (at_ base 1140) = Some W_5a2b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 285 _ HCODE eq_refl). Qed.
  Lemma Fo1144 : fetch_word segs (at_ base 1144) = Some W_5a2b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 286 _ HCODE eq_refl). Qed.
  Lemma Fo1148 : fetch_word segs (at_ base 1148) = Some W_5a2bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 287 _ HCODE eq_refl). Qed.
  Lemma Fo1152 : fetch_word segs (at_ base 1152) = Some W_5a2c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 288 _ HCODE eq_refl). Qed.



  Lemma Fo1168 : fetch_word segs (at_ base 1168) = Some W_5a2d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 292 _ HCODE eq_refl). Qed.
  Lemma Fo1172 : fetch_word segs (at_ base 1172) = Some W_5a2d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 293 _ HCODE eq_refl). Qed.
  Lemma Fo1176 : fetch_word segs (at_ base 1176) = Some W_5a2d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 294 _ HCODE eq_refl). Qed.
  Lemma Fo1180 : fetch_word segs (at_ base 1180) = Some W_5a2dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 295 _ HCODE eq_refl). Qed.
  Lemma Fo1184 : fetch_word segs (at_ base 1184) = Some W_5a2e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 296 _ HCODE eq_refl). Qed.
  Lemma Fo1188 : fetch_word segs (at_ base 1188) = Some W_5a2e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 297 _ HCODE eq_refl). Qed.
  Lemma Fo1192 : fetch_word segs (at_ base 1192) = Some W_5a2e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 298 _ HCODE eq_refl). Qed.
  Lemma Fo1196 : fetch_word segs (at_ base 1196) = Some W_5a2ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 299 _ HCODE eq_refl). Qed.
  Lemma Fo1200 : fetch_word segs (at_ base 1200) = Some W_5a2f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 300 _ HCODE eq_refl). Qed.
  Lemma Fo1204 : fetch_word segs (at_ base 1204) = Some W_5a2f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 301 _ HCODE eq_refl). Qed.
  Lemma Fo1208 : fetch_word segs (at_ base 1208) = Some W_5a2f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 302 _ HCODE eq_refl). Qed.
  Lemma Fo1212 : fetch_word segs (at_ base 1212) = Some W_5a2fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 303 _ HCODE eq_refl). Qed.
  Lemma Fo1216 : fetch_word segs (at_ base 1216) = Some W_5a300.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 304 _ HCODE eq_refl). Qed.
  Lemma Fo1220 : fetch_word segs (at_ base 1220) = Some W_5a304.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 305 _ HCODE eq_refl). Qed.
  Lemma Fo1224 : fetch_word segs (at_ base 1224) = Some W_5a308.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 306 _ HCODE eq_refl). Qed.
  Lemma Fo1228 : fetch_word segs (at_ base 1228) = Some W_5a30c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 307 _ HCODE eq_refl). Qed.



































































  Lemma Fo1592 : fetch_word segs (at_ base 1592) = Some W_5a478.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 398 _ HCODE eq_refl). Qed.
  Lemma Fo1596 : fetch_word segs (at_ base 1596) = Some W_5a47c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 399 _ HCODE eq_refl). Qed.
  Lemma Fo1600 : fetch_word segs (at_ base 1600) = Some W_5a480.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 400 _ HCODE eq_refl). Qed.
  Lemma Fo1604 : fetch_word segs (at_ base 1604) = Some W_5a484.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 401 _ HCODE eq_refl). Qed.
  Lemma Fo1608 : fetch_word segs (at_ base 1608) = Some W_5a488.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 402 _ HCODE eq_refl). Qed.
  Lemma Fo1612 : fetch_word segs (at_ base 1612) = Some W_5a48c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 403 _ HCODE eq_refl). Qed.
  Lemma Fo1616 : fetch_word segs (at_ base 1616) = Some W_5a490.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 404 _ HCODE eq_refl). Qed.
  Lemma Fo1620 : fetch_word segs (at_ base 1620) = Some W_5a494.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 405 _ HCODE eq_refl). Qed.
  Lemma Fo1624 : fetch_word segs (at_ base 1624) = Some W_5a498.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 406 _ HCODE eq_refl). Qed.
  Lemma Fo1628 : fetch_word segs (at_ base 1628) = Some W_5a49c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 407 _ HCODE eq_refl). Qed.
  Lemma Fo1632 : fetch_word segs (at_ base 1632) = Some W_5a4a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 408 _ HCODE eq_refl). Qed.
  Lemma Fo1636 : fetch_word segs (at_ base 1636) = Some W_5a4a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 409 _ HCODE eq_refl). Qed.
  Lemma Fo1640 : fetch_word segs (at_ base 1640) = Some W_5a4a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 410 _ HCODE eq_refl). Qed.
  Lemma Fo1644 : fetch_word segs (at_ base 1644) = Some W_5a4ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 411 _ HCODE eq_refl). Qed.
  Lemma Fo1648 : fetch_word segs (at_ base 1648) = Some W_5a4b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 412 _ HCODE eq_refl). Qed.
  Lemma Fo1652 : fetch_word segs (at_ base 1652) = Some W_5a4b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 413 _ HCODE eq_refl). Qed.
  Lemma Fo1656 : fetch_word segs (at_ base 1656) = Some W_5a4b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 414 _ HCODE eq_refl). Qed.
  Lemma Fo1660 : fetch_word segs (at_ base 1660) = Some W_5a4bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 415 _ HCODE eq_refl). Qed.
  Lemma Fo1664 : fetch_word segs (at_ base 1664) = Some W_5a4c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 unreg_words 416 _ HCODE eq_refl). Qed.
  Lemma Do0 : fetch_word segs (at_ dbase 0) = Some W_bf020.   (* [comment removed for export] *)
  Proof using DCODE. exact (code_ato_get segs dbase 0 dtor_words 0 _ DCODE eq_refl). Qed.
  Lemma Do4 : fetch_word segs (at_ dbase 4) = Some W_bf024.   (* [comment removed for export] *)
  Proof using DCODE. exact (code_ato_get segs dbase 0 dtor_words 1 _ DCODE eq_refl). Qed.
  Lemma Do36 : fetch_word segs (at_ dbase 36) = Some W_bf044.   (* [comment removed for export] *)
  Proof using DCODE. exact (code_ato_get segs dbase 0 dtor_words 9 _ DCODE eq_refl). Qed.
  Lemma Do40 : fetch_word segs (at_ dbase 40) = Some W_bf048.   (* [comment removed for export] *)
  Proof using DCODE. exact (code_ato_get segs dbase 0 dtor_words 10 _ DCODE eq_refl). Qed.
  Lemma Do44 : fetch_word segs (at_ dbase 44) = Some W_bf04c.   (* [comment removed for export] *)
  Proof using DCODE. exact (code_ato_get segs dbase 0 dtor_words 11 _ DCODE eq_refl). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma v_andi63_mul64 : forall n, (0 <= n)%Z -> (64 * n < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 (64 * n)) 63 = Z_to_bv 64 0.
  Proof using dbase base.
    intros n H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 63) with (Z.ones 6). rewrite u_Z2bv by lia.
    rewrite Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z. f_equal.
    rewrite Z.mul_comm, Z.mod_mul; lia.
  Qed.
  Lemma v_srai6_mul64 : forall n, (0 <= n)%Z -> (64 * n < 2 ^ 63)%Z -> v_srai (Z_to_bv 64 (64 * n)) 6 = Z_to_bv 64 n.
  Proof using dbase base.
    intros n H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold v_srai in G in change_no_check G' end). rewrite bv_signed_small by (rewrite u_Z2bv; lia). rewrite u_Z2bv by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z. f_equal. rewrite Z.mul_comm, Z.div_mul; lia.
  Qed.
  Lemma v_sub_mul64 : forall p n, (0 <= p)%Z -> (0 <= n)%Z -> (p + 64 * n < 2 ^ 64)%Z ->
    v_sub (Z_to_bv 64 (p + 64 * n)) (Z_to_bv 64 p) = Z_to_bv 64 (64 * n).
  Proof using dbase base. intros p n H0 H1 H2. (lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables vflag : word.        (* [comment removed for export] *)
  Variable cpm : byte.           (* [comment removed for export] *)
  Variable midend : word.        (* [comment removed for export] *)
  Variable thr : Z.              (* [comment removed for export] *)
  Variables pg ro : word.        (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  #[local] Abbreviation N := (Z.of_nat (length globs)).

  Hypothesis Hsp : (0x10007fff8000 + 272 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis Hret : ret_ok ra.
  (* [comment removed for export] *)
  Hypothesis Rgs : rdn segs mem (Z_to_bv 64 g_start) 8 = Some (LE8z p_start).
  Hypothesis Rge : rdn segs mem (Z_to_bv 64 g_stop) 8 = Some (LE8z (p_start + 64 * N)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 8 = Some (LE8 vflag).
  Hypothesis Hfl : U vflag <> 0%Z.
  Hypothesis Rga : rdn segs mem (Z_to_bv 64 g_aflags) 8 = Some (LE8z p_aflags).
  Hypothesis Rrg : rdn segs mem (Z_to_bv 64 (p_aflags + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Hypothesis Rmu : rdn segs mem (Z_to_bv 64 p_mu) 8 = Some (LE8z 0).
  Hypothesis Rini : rdn segs mem (Z_to_bv 64 c_inited) 1 = Some [Z_to_bv 8 1].
  Hypothesis Rcpm : rdn segs mem (Z_to_bv 64 c_cpm) 1 = Some [cpm].
  Hypothesis Hcpm : U cpm <> 0%Z.
  Hypothesis Rgsh : rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8z p_shoff).
  Hypothesis Rsh : rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8z 0x7fff8000).
  Hypothesis Rgmb : rdn segs mem (Z_to_bv 64 g_midbeg) 8 = Some (LE8z p_midbeg).
  Hypothesis Rmb : rdn segs mem (Z_to_bv 64 p_midbeg) 8 = Some (LE8z 0).
  Hypothesis Rgme : rdn segs mem (Z_to_bv 64 g_midend) 8 = Some (LE8z p_midend).
  Hypothesis Rme : rdn segs mem (Z_to_bv 64 p_midend) 8 = Some (LE8 midend).
  Hypothesis Rghe : rdn segs mem (Z_to_bv 64 g_hiend) 8 = Some (LE8z p_hiend).
  Hypothesis Rhe : rdn segs mem (Z_to_bv 64 p_hiend) 8 = Some (LE8z 0x7fffffffffff).
  Hypothesis Rgrms : rdn segs mem (Z_to_bv 64 g_rms) 8 = Some (LE8z p_rms).
  Hypothesis Rrms : rdn segs mem (Z_to_bv 64 p_rms) 8 = Some (LE8 mset).
  Hypothesis Rgcf : rdn segs mem (Z_to_bv 64 g_cfl) 8 = Some (LE8z p_cfl).
  Hypothesis Rthr : rdn segs mem (Z_to_bv 64 (p_cfl + 120)) 8 = Some (LE8z thr).
  Hypothesis Hthr : (0 <= thr < 2 ^ 64)%Z.
  Hypothesis Rpg : rdn segs mem (Z_to_bv 64 g_pgsz) 8 = Some (LE8 pg).
  Hypothesis Rro : rdn segs mem (Z_to_bv 64 c_ro) 8 = Some (LE8 ro).
  (* [comment removed for export] *)
  Definition ug_cells : list Z :=
    g_start :: g_stop :: p_flag :: g_aflags :: p_aflags :: (p_aflags + 24)%Z :: c_inited :: g_pgsz :: c_ro :: poison_cells pt.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= 0x7fff8000)%Z ug_cells.
  Hypothesis Hcells_mu : Forall (fun c => c + 8 <= p_mu \/ p_mu + 8 <= c)%Z ug_cells.
  Hypothesis Hmu : (64 <= p_mu)%Z /\ (p_mu + 16 <= 0x7fff8000)%Z /\ (p_mu mod 8 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis HN : (1 <= N)%Z.
  Hypothesis Hps : (0 <= p_start)%Z /\ (p_start mod 8 = 0)%Z /\ (p_start + 64 * N <= 0x7fff8000)%Z /\ (8 * N < thr)%Z.
  Hypothesis Hps_mu : (p_start + 64 * N <= p_mu \/ p_mu + 8 <= p_start)%Z.
  Hypothesis HG : forall i b s, nth_error globs i = Some (b, s) ->
    rdn segs mem (Z_to_bv 64 (p_start + 64 * Z.of_nat i)) 8 = Some (LE8z b)
    /\ rdn segs mem (Z_to_bv 64 (p_start + 64 * Z.of_nat i + 16)) 8 = Some (LE8z s)
    /\ rdn segs mem (Z_to_bv 64 (p_start + 64 * Z.of_nat i + 56)) 8 = Some (LE8z (2 ^ 64 - 1))
    /\ (0 <= b)%Z /\ (b mod 8 = 0)%Z /\ (s mod 8 = 0)%Z /\ (8 <= s)%Z /\ (b + s <= 0x7fff8000)%Z /\ (s / 8 < thr)%Z
    /\ store_ok segs mem (Z_to_bv 64 (zshad b)) (Z.to_nat (s / 8)) = true.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok segs mem (at_ sp (-272)) 272 = true.
  Hypothesis Hmu_ok : store_ok segs mem (Z_to_bv 64 p_mu) 8 = true.
  Hypothesis Hfl_ok : store_ok segs mem (Z_to_bv 64 p_flag) 8 = true.
  Hypothesis Hshd : store_ok segs mem (Z_to_bv 64 (zshad p_start)) (Z.to_nat (8 * N)) = true.
  Hypothesis Hmset_ok : ret_ok mset.
  Hypothesis Hmset_nz : U mset <> 0%Z.

  (* [comment removed for export] *)
  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold ug_cells, poison_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Lemma cell_mu : forall c k, In c ug_cells -> (k <= 8)%nat -> (c + Z.of_nat k <= p_mu \/ p_mu + 8 <= c)%Z.
  Proof using Hps Hmu Hcells_mu thr globs p_start dbase base. intros c k Hc Hk. pose proof (proj1 (Forall_forall _ _) Hcells_mu c Hc) as H. cbn beta in H. lia. Qed.
  (* [comment removed for export] *)
  Ltac mu_off := first [ apply cell_mu; [clear; (lazymatch goal with |- ?G => let G' := eval cbn [ug_cells poison_cells In] in G in change_no_check G' end); am_tauto | lia] | lia ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation s0e := (getr regs 8).
  (* [comment removed for export] *)
  Definition UM1 : word -> option byte := wbytes mem (at_ sp (-8)) (LE8 ra).
  (* [comment removed for export] *)
  Definition UM2 : word -> option byte :=
    wbytes (wbytes UM1 (at_ sp (-24)) (LE8 (at_ dbase 36))) (at_ sp (-32)) (LE8 s0e).
  (* [comment removed for export] *)
  Definition UM3 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes UM2
      (at_ sp (-40)) (LE8 (at_ base 1648)))
      (at_ sp (-48)) (LE8z p_flag))
      (at_ sp (-56)) (LE8 (getr regs 9)))
      (at_ sp (-64)) (LE8 (getr regs 18)))
      (at_ sp (-72)) (LE8 (getr regs 19)))
      (at_ sp (-80)) (LE8 (getr regs 20)))
      (at_ sp (-88)) (LE8 (getr regs 21)))
      (at_ sp (-96)) (LE8 (getr regs 22)))
      (at_ sp (-104)) (LE8 (getr regs 23)))
      (at_ sp (-112)) (LE8 (getr regs 24)))
      (at_ sp (-120)) (LE8 (getr regs 25)))
      (at_ sp (-128)) (LE8 (getr regs 26)))
      (at_ sp (-136)) (LE8 (getr regs 27)))
      (at_ sp (-176)) (LE8z p_start))
      (at_ sp (-200)) (LE8z (p_mu + 8)).
  (* [comment removed for export] *)
  Definition UMB : word -> option byte := wbytes UM3 (Z_to_bv 64 p_mu) (LE8z 1152921504606846976).
  (* [comment removed for export] *)
  Definition UMC : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes UMB
      (at_ sp (-192)) (LE8z (p_mu - 64)))
      (at_ sp (-184)) (LE8z N))
      (at_ sp (-144)) (LE8z p_midbeg))
      (at_ sp (-152)) (LE8z p_midend))
      (at_ sp (-168)) (LE8z p_hiend))
      (at_ sp (-160)) (LE8 pg).
  (* [comment removed for export] *)
  Definition UMD : word -> option byte := shz UMC globs.
  (* [comment removed for export] *)
  Definition UME : word -> option byte :=
    wbytes (ps_frame UMD (at_ sp (-208)) (at_ base 988) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 1) (Z_to_bv 64 2) v_str
                     (Z_to_bv 64 (p_start + 64 * N)) (Z_to_bv 64 2305843009213693952))
           (Z_to_bv 64 (zshad p_start)) (repeat (cbyte (Z_to_bv 64 0)) (Z.to_nat (8 * N))).
  (* [comment removed for export] *)
  Definition UMF : word -> option byte := wbytes UME (Z_to_bv 64 p_mu) (LE8z 0).
  (* [comment removed for export] *)
  Definition UMG : word -> option byte := wbytes UMF (Z_to_bv 64 p_flag) (LE8z 0).

  (* [comment removed for export] *)
  Ltac grows_tac :=
    repeat (lazymatch goal with
            | |- mem_grows ?a ?a => apply mem_grows_refl
            | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
            end).
  Lemma UM1_grows : mem_grows mem UM1. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UM1 in G in change_no_check G' end). grows_tac. Qed.
  Lemma UM2_grows : mem_grows mem UM2. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UM2 in G in change_no_check G' end). eapply mem_grows_trans; [apply UM1_grows|]. grows_tac. Qed.
  Lemma UM3_grows : mem_grows mem UM3. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UM3 in G in change_no_check G' end). eapply mem_grows_trans; [apply UM2_grows|]. grows_tac. Qed.
  Lemma UMB_grows : mem_grows mem UMB. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UMB in G in change_no_check G' end). eapply mem_grows_trans; [apply UM3_grows|]. grows_tac. Qed.
  Lemma UMC_grows : mem_grows mem UMC. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UMC in G in change_no_check G' end). eapply mem_grows_trans; [apply UMB_grows|]. grows_tac. Qed.
  Lemma shz_grows : forall l M, mem_grows M (shz M l).
  Proof using.
    induction l as [|[b s] l IH]; intros M; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [shz] in G in change_no_check G' end).
    eapply mem_grows_trans; [apply wbytes_grows | apply IH].
  Qed.
  Lemma UMD_grows : mem_grows mem UMD. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UMD in G in change_no_check G' end). eapply mem_grows_trans; [apply UMC_grows | apply shz_grows]. Qed.

  (* [comment removed for export] *)
  Lemma UM1_out : forall x : word, (U x < U sp - 8 \/ U sp <= U x)%Z -> UM1 x = mem x.
  Proof using Hsp globs p_mu p_start dbase base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold UM1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma UM2_out : forall x : word, (U x < U sp - 32 \/ U sp <= U x)%Z -> UM2 x = mem x.
  Proof using Hsp globs p_mu p_start base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold UM2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply UM1_out; lia| | | |]; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma UM3_out : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> UM3 x = mem x.
  Proof using Hsp globs.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold UM3 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply UM2_out; lia| ..]; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.

  Lemma UM2_o1 : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> UM2 x = mem x.
  Proof using Hsp globs p_mu p_start base. intros x Hx. apply UM2_out. lia. Qed.
  Lemma UMB_out : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z -> UMB x = mem x.
  Proof using Hmu Hsp globs.
    intros x Hx Hm. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold UMB in G in change_no_check G' end).
    rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply UM3_out; exact Hx| |]; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ].
  Qed.
  Lemma UMC_out : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z -> UMC x = mem x.
  Proof using Hmu Hsp.
    intros x Hx Hm. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold UMC in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply UMB_out; assumption| ..]; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma shz_out : forall l M (x : word),
    Forall (fun bs => 0 <= fst bs /\ fst bs mod 8 = 0 /\ fst bs + snd bs <= 0x7fff8000 /\ 8 <= snd bs)%Z l ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> shz M l x = M x.
  Proof using Hps Hmu thr globs p_mu p_start dbase base.
    induction l as [|[b s] l IH]; intros M x Hl Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [shz] in G in change_no_check G' end).
    apply Forall_cons_iff in Hl as [[Hb [Hb8 [Hbs Hs]]] Hl]. cbn [fst snd] in Hb, Hb8, Hbs, Hs.
    rewrite IH by assumption. (lazymatch goal with |- ?G => let G' := eval unfold zshad in G in change_no_check G' end).
    pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono s (0x7fff8000 - b) 8 ltac:(lia) ltac:(lia)) as Hd.
    replace ((0x7fff8000 - b) / 8)%Z with (0xffff000 - b / 8)%Z in Hd
      by (replace (0x7fff8000 - b)%Z with ((0xffff000 - b / 8) * 8)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
    apply wbytes_outside; rewrite repeat_length, Z2Nat.id by lia; wd_ulia.
  Qed.
  Lemma globs_ok : Forall (fun bs => 0 <= fst bs /\ fst bs mod 8 = 0 /\ fst bs + snd bs <= 0x7fff8000 /\ 8 <= snd bs)%Z globs.
  Proof using HG Hmu thr mem p_mu p_start dbase base segs.
    apply Forall_forall. intros [b s] Hin. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
    destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (HG i b s Hi) as (_ & _ & _ & Hb & Hb8 & _ & Hs & Hbs & _). lia.
  Qed.
  Lemma UMD_out : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UMD x = mem x.
  Proof using HG Hps Hmu Hsp thr segs. intros x Hx Hm Hs. (lazymatch goal with |- ?G => let G' := eval unfold UMD in G in change_no_check G' end). rewrite (shz_out globs UMC x globs_ok Hs). apply UMC_out; assumption. Qed.

  (* [comment removed for export] *)
  Lemma rd_cell : forall (M : word -> option byte) (c : Z) k bs,
    (forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
                      (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= 0x7fff8000)%Z -> (c + Z.of_nat k <= p_mu \/ p_mu + 8 <= c)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs -> rdn segs M (Z_to_bv 64 c) k = Some bs.
  Proof using Hps Hmu Hsp thr globs p_start dbase base.
    intros M c k bs HM Hc Hk Hm Hr. pose proof (u64_range sp). rewrite <- Hr. apply rdn_ext; [wd_ulia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply HM; lia.
  Qed.
  Lemma UM1_o3 : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UM1 x = mem x.
  Proof using Hsp globs p_start dbase base. intros x Hx _ _. apply UM1_out. lia. Qed.
  Lemma UM2_o3 : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UM2 x = mem x.
  Proof using Hsp globs p_start base. intros x Hx _ _. apply UM2_out. lia. Qed.

  Lemma UMB_o3 : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UMB x = mem x.
  Proof using Hmu Hsp globs. intros x Hx Hm _. apply UMB_out; assumption. Qed.
  Lemma UMC_o3 : forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UMC x = mem x.
  Proof using Hmu Hsp. intros x Hx Hm _. apply UMC_out; assumption. Qed.

  (* [comment removed for export] *)
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          first [ eapply store_ok_mono; [ first [apply UMC_grows | apply UMB_grows | apply UM3_grows | apply UM2_grows | apply UM1_grows] |] | idtac ];
          eapply (store_ok_sub segs mem (at_ sp (-272)) _ 272);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac cld F D vv MO Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?v_addi_0; try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm);
          apply (rd_cell _ _ _ _ MO); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | mu_off | exact Hr]
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac fld F D vv UNF :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; UNF; rd8_chain
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  #[local] Abbreviation CLX := (fun r : reg => In r [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkDE :
    exists r,
      msteps segs (mkst regs (at_ dbase 0) mem rom) (mkst r (at_ base 0) UM2 rom)
      /\ getr r 1 = at_ base 1648 /\ getr r 2 = at_ sp (-32) /\ getr r 8 = Z_to_bv 64 p_flag
      /\ getr r 10 = Z_to_bv 64 p_start /\ getr r 11 = Z_to_bv 64 N /\ getr r 14 = Z_to_bv 64 0
      /\ (forall i : reg, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using Hstk Hps_mu Hps HN Hmu Hcells_mu Hcells Hfl Rfl Rge Rgs R2 R1 Hsp thr vflag DJ32 DG24 DG12 DG8 DCODE HCODE c_ro c_inited g_pgsz p_mu p_aflags g_aflags g_stop g_start pt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dbase) as Hdr. cells_split.
    destruct Hps as (P0 & P8 & Pend & PN).
    destruct DG8 as (x8 & DG8a & DG8b). destruct DG12 as (x12 & DG12a & DG12b). destruct DG24 as (x24 & DG24r).
    wd_eexists. split.
    - an Do0 D_bf020.                                   (* [comment removed for export] *)
      fsd Do4 D_bf024 (at_ sp (-8)).                    (* [comment removed for export] *)
      change (wbytes _ _ _) with UM1.
      eapply msteps_trans; [apply DG8a|]. zlit_at.         (* [comment removed for export] *)
      eapply msteps_trans; [apply DG12a|]. zlit_at.        (* [comment removed for export] *)
      eapply msteps_trans; [eapply DG8b; [gres; reflexivity | apply (rd_cell _ _ _ _ UM1_o3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rgs]]|]. zlit_at.  (* [comment removed for export] *)
      eapply msteps_trans; [eapply DG12b; [gres; reflexivity | apply (rd_cell _ _ _ _ UM1_o3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rge]]|]. zlit_at. (* [comment removed for export] *)
      eapply msteps_trans; [apply DG24r|]. zlit_at.        (* [comment removed for export] *)
      eapply msteps_trans; [apply DJ32|]. zlit_at.         (* [comment removed for export] *)
      an Fo1592 D_5a478.                                 (* [comment removed for export] *)
      fsd Fo1596 D_5a47c (at_ sp (-24)).                 (* [comment removed for export] *)
      fsd Fo1600 D_5a480 (at_ sp (-32)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with UM2.
      ab_ft Fo1604 D_5a484 ltac:(unorm; condz).          (* [comment removed for export] *)
      an Fo1608 D_5a488.                                 (* [comment removed for export] *)
      cld Fo1612 D_5a48c vflag UM2_o3 Rfl.               (* [comment removed for export] *)
      ab_ft Fo1616 D_5a490 ltac:(condz).                 (* [comment removed for export] *)
      av Fo1620 D_5a494 (Z_to_bv 64 (64 * N)) ltac:(apply v_sub_mul64; lia).   (* [comment removed for export] *)
      av Fo1624 D_5a498 (Z_to_bv 64 0) ltac:(apply v_andi63_mul64; lia).        (* [comment removed for export] *)
      ab_ft Fo1628 D_5a49c ltac:(condz).                 (* [comment removed for export] *)
      av Fo1632 D_5a4a0 (Z_to_bv 64 N) ltac:(apply v_srai6_mul64; lia).         (* [comment removed for export] *)
      an Fo1636 D_5a4a4.                                 (* [comment removed for export] *)
      an Fo1640 D_5a4a8.                                 (* [comment removed for export] *)
      an Fo1644 D_5a4ac.                                 (* [comment removed for export] *)
      wd_refl.
    - post.
      + intros i Hi. cbn [In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]). destruct Hi.
      + ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_low : forall (M : word -> option byte) (c : Z) k bs,
    (forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= 0x7fff8000)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs -> rdn segs M (Z_to_bv 64 c) k = Some bs.
  Proof using Hps Hmu Hsp thr globs p_mu p_start dbase base.
    intros M c k bs HM Hc Hk Hr. pose proof (u64_range sp). rewrite <- Hr. apply rdn_ext; [wd_ulia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply HM; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac rd_peel MO Hr :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    apply (rd_cell _ _ _ _ MO); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | mu_off | exact Hr].
  (* [comment removed for export] *)
  Ltac rd_peel0 MO Hr :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    apply (rd_low _ _ _ _ MO); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
  (* [comment removed for export] *)
  Ltac cldc F D cc vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            replace a with (Z_to_bv 64 cc : word) by (rewrite ?v_addi_0; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia) end;
          RD
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Lemma blkU1 : forall r0,
    getr r0 1 = at_ base 1648 -> getr r0 2 = at_ sp (-32) -> getr r0 8 = Z_to_bv 64 p_flag ->
    getr r0 10 = Z_to_bv 64 p_start -> getr r0 11 = Z_to_bv 64 N ->
    (forall i : reg, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr r0 i = getr regs i) ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 0) UM2 rom) (mkst r (at_ base 168) UM3 rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 12 = Z_to_bv 64 0 /\ getr r 13 = Z_to_bv 64 1152921504606846976
      /\ getr r 14 = Z_to_bv 64 1152921504606846976 /\ getr r 21 = Z_to_bv 64 2305843009213693952 /\ getr r 22 = Z_to_bv 64 (p_mu - 64)
      /\ getr r 23 = Z_to_bv 64 N /\ getr r 24 = Z_to_bv 64 p_mu /\ getr r 25 = Z_to_bv 64 p_aflags
      /\ regs_agree CLX regs r.
  Proof using Hstk Hps Hmu Hcells_mu Hcells Rmu Rrg Rga Hsp thr G84 G60 HCODE c_ro c_inited g_pgsz g_aflags g_stop g_start pt.
    intros r0 Q1 Q2 Q8 Q10 Q11 QK AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. cells_split.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    assert (Q9 : getr r0 9 = getr regs 9) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q18 : getr r0 18 = getr regs 18) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q19 : getr r0 19 = getr regs 19) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q20 : getr r0 20 = getr regs 20) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q21 : getr r0 21 = getr regs 21) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q22 : getr r0 22 = getr regs 22) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q23 : getr r0 23 = getr regs 23) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q24 : getr r0 24 = getr regs 24) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q25 : getr r0 25 = getr regs 25) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q26 : getr r0 26 = getr regs 26) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    assert (Q27 : getr r0 27 = getr regs 27) by (apply QK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto).
    destruct G60 as (x60 & G60r). destruct G84 as (x84 & G84a & G84b).
    wd_eexists. split.
    - an Fo0 D_59e40.                                    (* [comment removed for export] *)
      fsd Fo4 D_59e44 (at_ sp (-40)).                    (* [comment removed for export] *)
      fsd Fo8 D_59e48 (at_ sp (-48)).                    (* [comment removed for export] *)
      fsd Fo12 D_59e4c (at_ sp (-56)).                   (* [comment removed for export] *)
      fsd Fo16 D_59e50 (at_ sp (-64)).                   (* [comment removed for export] *)
      fsd Fo20 D_59e54 (at_ sp (-72)).                   (* [comment removed for export] *)
      fsd Fo24 D_59e58 (at_ sp (-80)).                   (* [comment removed for export] *)
      fsd Fo28 D_59e5c (at_ sp (-88)).                   (* [comment removed for export] *)
      fsd Fo32 D_59e60 (at_ sp (-96)).                   (* [comment removed for export] *)
      fsd Fo36 D_59e64 (at_ sp (-104)).                  (* [comment removed for export] *)
      fsd Fo40 D_59e68 (at_ sp (-112)).                  (* [comment removed for export] *)
      fsd Fo44 D_59e6c (at_ sp (-120)).                  (* [comment removed for export] *)
      fsd Fo48 D_59e70 (at_ sp (-128)).                  (* [comment removed for export] *)
      fsd Fo52 D_59e74 (at_ sp (-136)).                  (* [comment removed for export] *)
      an Fo56 D_59e78.                                   (* [comment removed for export] *)
      eapply msteps_trans; [eapply G60r; rd_peel UM2_o3 Rga|]. zlit_at.    (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 1)) (v := Z_to_bv 64 1);
          [exact Fo68 | reflexivity | exact D_59e84
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rd_peel UM2_o3 Rrg
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      fsd Fo72 D_59e88 (at_ sp (-176)).                  (* [comment removed for export] *)
      ab_ft Fo76 D_59e8c ltac:(condz).                   (* [comment removed for export] *)
      an Fo80 D_59e90.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply G84a|]. zlit_at.       (* [comment removed for export] *)
      an Fo88 D_59e98.                                   (* [comment removed for export] *)
      an Fo92 D_59e9c.                                   (* [comment removed for export] *)
      an Fo96 D_59ea0.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply G84b; gres; reflexivity|]. zlit_at.   (* [comment removed for export] *)
      an Fo104 D_59ea8.                                  (* [comment removed for export] *)
      an Fo108 D_59eac.                                  (* [comment removed for export] *)
      an Fo112 D_59eb0.                                  (* [comment removed for export] *)
      cldc Fo116 D_59eb4 p_mu (Z_to_bv 64 0 : word) ltac:(rd_peel0 UM2_o1 Rmu).       (* [comment removed for export] *)
      an Fo120 D_59eb8.                                  (* [comment removed for export] *)
      av Fo124 D_59ebc (Z_to_bv 64 p_mu : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).        (* [comment removed for export] *)
      av Fo128 D_59ec0 (Z_to_bv 64 (p_mu + 8) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      fsd Fo132 D_59ec4 (at_ sp (-200)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with UM3.
      an Fo136 D_59ec8.                                  (* [comment removed for export] *)
      an Fo140 D_59ecc.                                  (* [comment removed for export] *)
      an Fo144 D_59ed0.                                  (* [comment removed for export] *)
      an Fo148 D_59ed4.                                  (* [comment removed for export] *)
      an Fo152 D_59ed8.                                  (* [comment removed for export] *)
      ab_ft Fo156 D_59edc ltac:(condz).                 (* [comment removed for export] *)
      an Fo160 D_59ee0.                                  (* [comment removed for export] *)
      an Fo164 D_59ee4.                                  (* [comment removed for export] *)
      wd_refl.
    - post; try (apply bv_eq; vm_compute; reflexivity). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkU2 : forall r0,
    getr r0 2 = at_ sp (-208) -> getr r0 12 = Z_to_bv 64 0 -> getr r0 13 = Z_to_bv 64 1152921504606846976 ->
    getr r0 14 = Z_to_bv 64 1152921504606846976 -> getr r0 21 = Z_to_bv 64 2305843009213693952 -> getr r0 22 = Z_to_bv 64 (p_mu - 64) ->
    getr r0 23 = Z_to_bv 64 N -> getr r0 24 = Z_to_bv 64 p_mu -> getr r0 25 = Z_to_bv 64 p_aflags ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 168) UM3 rom) (mkst r (at_ base 444) UMC rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 9 = Z_to_bv 64 p_cfl /\ getr r 18 = Z_to_bv 64 2 /\ getr r 19 = v_str
      /\ getr r 20 = Z_to_bv 64 p_start /\ getr r 21 = Z_to_bv 64 2305843009213693952 /\ getr r 22 = Z_to_bv 64 (p_mu - 64)
      /\ getr r 23 = Z_to_bv 64 p_rms /\ getr r 24 = Z_to_bv 64 p_mu /\ getr r 25 = Z_to_bv 64 p_aflags
      /\ getr r 26 = Z_to_bv 64 p_shoff /\ getr r 27 = Z_to_bv 64 N
      /\ regs_agree CLX regs r.
  Proof using Hmu_ok Hstk Hps_mu Hps HN Hmu Hcells_mu Hcells Rpg Rgcf Rgrms Rghe Rgme Rgmb Rgsh Rmu Hsp thr G388 G336 G332 G328 G324 G320 G316 G312 HCODE c_ro c_inited g_pgsz g_aflags g_stop g_start.
    intros r0 Q2 Q12 Q13 Q14 Q21 Q22 Q23 Q24 Q25 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. cells_split.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    destruct G312 as (x312 & G312a & G312b). destruct G316 as (x316 & G316a & G316b). destruct G320 as (x320 & G320a & G320b).
    destruct G324 as (x324 & G324a & G324b). destruct G328 as (x328 & G328a & G328b). destruct G332 as (x332 & G332a & G332b).
    destruct G336 as (x336 & G336a & G336b). destruct G388 as (x388 & G388r).
    wd_eexists. split.
    - (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run segs r0 (at_ base 168) (at_ base 172) (at_ base 176) (at_ base 180) (at_ base 184) UM3 rom
                  _ _ _ _ _ _ _ _ 13 24 15 14 13 12 BC_NE _ _ (LE8z 0) (Z_to_bv 64 0)
                  Fo168 eq_refl D_59ee8 Fo172 eq_refl D_59eec Fo176 eq_refl D_59ef0 Fo180 eq_refl D_59ef4);
          rewrite ?at_addi; try reflexivity.
        all: lazymatch goal with
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => rewrite Q24; unorm; exact Mal
             | |- rdn _ _ _ _ = _ => rewrite Q24; rd_peel0 UM3_out Rmu
             | |- store_ok _ _ _ _ = true => rewrite Q24; eapply store_ok_mono; [apply UM3_grows | exact Hmu_ok]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite Q12; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rewrite Q24.
      change (wbytes UM3 (Z_to_bv 64 p_mu) (LE8 (Z_to_bv 64 1152921504606846976))) with UMB.
      ab_tk Fo184 D_59ef8 ltac:(condz).                 (* [comment removed for export] *)
      fsd Fo300 D_59f6c (at_ sp (-192)).                 (* [comment removed for export] *)
      fsd Fo304 D_59f70 (at_ sp (-184)).                 (* [comment removed for export] *)
      ab_ft Fo308 D_59f74 ltac:(unorm; condz).           (* [comment removed for export] *)
      eapply msteps_trans; [apply G312a|]. zlit_at.
      eapply msteps_trans; [apply G316a|]. zlit_at.
      eapply msteps_trans; [apply G320a|]. zlit_at.
      eapply msteps_trans; [apply G324a|]. zlit_at.
      eapply msteps_trans; [apply G328a|]. zlit_at.
      eapply msteps_trans; [apply G332a|]. zlit_at.
      eapply msteps_trans; [apply G336a|]. zlit_at.
      eapply msteps_trans; [eapply G312b; [gres; reflexivity | rd_peel UMB_o3 Rgsh]|]. zlit_at.   (* [comment removed for export] *)
      eapply msteps_trans; [eapply G316b; [gres; reflexivity | rd_peel UMB_o3 Rgmb]|]. zlit_at.   (* [comment removed for export] *)
      fsd Fo348 D_59f9c (at_ sp (-144)).                 (* [comment removed for export] *)
      eapply msteps_trans; [eapply G320b; [gres; reflexivity | rd_peel UMB_o3 Rgme]|]. zlit_at.   (* [comment removed for export] *)
      fsd Fo356 D_59fa4 (at_ sp (-152)).                 (* [comment removed for export] *)
      eapply msteps_trans; [eapply G324b; [gres; reflexivity | rd_peel UMB_o3 Rghe]|]. zlit_at.   (* [comment removed for export] *)
      fsd Fo364 D_59fac (at_ sp (-168)).                 (* [comment removed for export] *)
      eapply msteps_trans; [eapply G328b; [gres; reflexivity | rd_peel UMB_o3 Rgcf]|]. zlit_at.   (* [comment removed for export] *)
      eapply msteps_trans; [eapply G332b; [gres; reflexivity | rd_peel UMB_o3 Rgrms]|]. zlit_at.  (* [comment removed for export] *)
      eapply msteps_trans; [eapply G336b; [gres; reflexivity | rd_peel UMB_o3 Rpg]|]. zlit_at.    (* [comment removed for export] *)
      fsd Fo380 D_59fbc (at_ sp (-160)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with UMC.
      an Fo384 D_59fc0.                                  (* [comment removed for export] *)
      eapply msteps_trans; [apply G388r|]. zlit_at.      (* [comment removed for export] *)
      fld Fo396 D_59fcc (Z_to_bv 64 p_start : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold UMC, UMB, UM3 in G in change_no_check G' end)).   (* [comment removed for export] *)
      fld Fo400 D_59fd0 (Z_to_bv 64 N : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold UMC in G in change_no_check G' end)).                   (* [comment removed for export] *)
      an Fo404 D_59fd4.                                  (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition memI (M : word -> option byte) : Prop :=
    (forall x : word, (U x < U sp - 208 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
                      (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> M x = mem x)
    /\ mem_grows mem M.

  Lemma memI_shz1 : forall M b s, memI M -> (0 <= b)%Z -> (b mod 8 = 0)%Z -> (b + s <= 0x7fff8000)%Z -> (8 <= s)%Z ->
    memI (shz M [(b, s)]).
  Proof using Hps Hmu thr globs p_start dbase base.
    intros M b s [MO MG] Hb Hb8 Hbs Hs. split.
    - intros x H1 H2 H3. rewrite (shz_out [(b, s)] M x); [apply MO; assumption | | exact H3].
      constructor; [(lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia | constructor].
    - (lazymatch goal with |- ?G => let G' := eval cbn [shz] in G in change_no_check G' end). eapply mem_grows_trans; [exact MG | apply wbytes_grows].
  Qed.

  Lemma byte_of_word : forall s, Z_to_bv 8 (U (Z_to_bv 64 s)) = Z_to_bv 8 s.
  Proof using.
    intros s. apply bv_eq. rewrite !(Z_to_bv_unsigned 8), (Z_to_bv_unsigned 64). (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end).
    change (bv_modulus 8) with 256%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
    apply Z.mod_mod_divide. exists (2 ^ 56)%Z. reflexivity.
  Qed.
  Lemma lowbyte_mod8 : forall s, (s mod 8 = 0)%Z -> (U (Z_to_bv 64 (U (Z_to_bv 8 s))) mod 8 = 0)%Z.
  Proof using globs p_mu p_start dbase base.
    intros s Hs8. rewrite (Z_to_bv_unsigned 8). (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 8) with 256%Z.
    pose proof (Z.mod_pos_bound s 256 ltac:(lia)).
    rewrite u_Z2bv by lia.
    rewrite (Z.mod_mod_divide _ 256 8) by (exists 32%Z; reflexivity). exact Hs8.
  Qed.

  Lemma shadow_end_eq : forall b s, (0 <= b)%Z -> (b mod 8 = 0)%Z -> (s mod 8 = 0)%Z -> (8 <= s)%Z ->
    ((b + s - 8) / 8 + 1 = b / 8 + s / 8)%Z.
  Proof using Hps Hmu thr globs p_mu p_start dbase base.
    intros b s Hb Hb8 Hs8 Hs. pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.div_mod s 8 ltac:(lia)).
    replace (b + s - 8)%Z with ((b / 8 + s / 8 - 1) * 8)%Z by lia. rewrite Z.div_mul by lia. lia.
  Qed.

  Lemma nth_lt : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
  Proof using.
    intros A l i x H. destruct (Nat.lt_ge_cases i (length l)) as [L|L]; [exact L|].
    apply (proj2 (nth_error_None l i)) in L. rewrite L in H. discriminate H.
  Qed.

  (* [comment removed for export] *)
  Lemma ug_iterA : forall (M : word -> option byte) r0 (i : nat) (b s : Z),
    memI M -> nth_error globs i = Some (b, s) ->
    getr r0 2 = at_ sp (-208) -> getr r0 9 = Z_to_bv 64 p_cfl -> getr r0 18 = Z_to_bv 64 2 ->
    getr r0 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat i) -> getr r0 23 = Z_to_bv 64 p_rms ->
    getr r0 25 = Z_to_bv 64 p_aflags -> getr r0 26 = Z_to_bv 64 p_shoff ->
    exists r,
      msteps segs (mkst r0 (at_ base 444) M rom) (mkst r (at_ mset 0) M rom)
      /\ getr r 1 = at_ base 420 /\ getr r 2 = at_ sp (-208) /\ getr r 10 = Z_to_bv 64 (zshad b)
      /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 (s / 8)
      /\ getr r 8 = Z_to_bv 64 (zshad b + s / 8)
      /\ (forall x : reg, In x [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr r x = getr r0 x)
      /\ regs_agree CLX r0 r.
  Proof using Hmset_ok HG Hps_mu Hps Hmu Hcells_mu Hcells Hthr Rthr Rrms Rsh Hcpm Rcpm Rini Rrg Hsp thr cpm Hbase HCPM HAI HCODE c_ro c_inited g_pgsz g_aflags p_flag g_stop g_start dbase.
    intros M r0 i b s [MO MG] Hi Q2 Q9 Q18 Q20 Q23 Q25 Q26.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. cells_split.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    destruct (HG i b s Hi) as (Rb & Rs & Rodr & Hb & Hb8 & Hs8 & Hs & Hbs & Hsthr & STb).
    pose proof (nth_lt _ _ _ Hi) as Hilen. apply Nat2Z.inj_lt in Hilen.
    pose proof (Z.div_mod b 8 ltac:(lia)) as Hbq. pose proof (Z.div_mod s 8 ltac:(lia)) as Hsq.
    pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)) as Hbq0. pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)) as Hsq0.
    wd_eexists. split.
    - an Fo444 D_59ffc.                                  (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply HAI; [ | | gres; reflexivity]; [ rd_peel MO Rini | apply ret_ok_at; [lia | reflexivity | lia] ]. }
      ab_ft Fo448 D_5a000 ltac:(condz).                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 1)) (v := Z_to_bv 64 1);
          [exact Fo452 | reflexivity | exact D_5a004
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rd_peel MO Rrg
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      ab_tk Fo456 D_5a008 ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft Fo476 D_5a01c ltac:(condz).                 (* [comment removed for export] *)
      cldc Fo480 D_5a020 (pt_p_shoff pt) (Z_to_bv 64 0x7fff8000 : word) ltac:(rd_peel MO Rsh).            (* [comment removed for export] *)
      cldc Fo484 D_5a024 (p_start + 64 * Z.of_nat i)%Z (Z_to_bv 64 b : word) ltac:(rd_peel MO Rb). (* [comment removed for export] *)
      an Fo488 D_5a028.                                  (* [comment removed for export] *)
      an Fo492 D_5a02c.                                  (* [comment removed for export] *)
      an Fo496 D_5a030.                                  (* [comment removed for export] *)
      an Fo500 D_5a034.                                  (* [comment removed for export] *)
      ab_tk Fo504 D_5a038 ltac:(condz).                 (* [comment removed for export] *)
      av Fo732 D_5a11c (Z_to_bv 64 0 : word) ltac:(apply v_andi_7_aligned; unorm; exact Hb8).   (* [comment removed for export] *)
      ab_ft Fo736 D_5a120 ltac:(condz).                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 s);
          [exact Fo740 | reflexivity | exact D_5a124
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm;
            rewrite <- (byte_of_word s); change [Z_to_bv 8 (U (Z_to_bv 64 s))] with (firstn 1 (LE8z s));
            lazymatch goal with |- rdn _ _ ?a _ = _ =>
              replace a with (Z_to_bv 64 (p_start + 64 * Z.of_nat i + 16) : word) by (f_equal; lia) end;
            apply (rdn_firstn segs M 8); [rd_peel MO Rs | lia] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av Fo744 D_5a128 (Z_to_bv 64 0 : word) ltac:(try unorm; apply v_andi_7_aligned; first [apply lowbyte_mod8; exact Hs8 | idtac]).  (* [comment removed for export] *)
      ab_ft Fo748 D_5a12c ltac:(condz).                 (* [comment removed for export] *)
      an Fo752 D_5a130.                                  (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply HCPM; [ | | | gres; reflexivity]; [ rd_peel MO Rcpm | exact Hcpm | apply ret_ok_at; [lia | reflexivity | lia] ]. }
      ab_ft Fo756 D_5a134 ltac:(condz).                 (* [comment removed for export] *)
      cldc Fo760 D_5a138 (p_start + 64 * Z.of_nat i)%Z (Z_to_bv 64 b : word) ltac:(rd_peel MO Rb).        (* [comment removed for export] *)
      cldc Fo764 D_5a13c (p_start + 64 * Z.of_nat i + 16)%Z (Z_to_bv 64 s : word) ltac:(rd_peel MO Rs).   (* [comment removed for export] *)
      cldc Fo768 D_5a140 (pt_p_shoff pt) (Z_to_bv 64 0x7fff8000 : word) ltac:(rd_peel MO Rsh).                    (* [comment removed for export] *)
      av Fo772 D_5a144 (Z_to_bv 64 (b / 8) : word) ltac:(rewrite v_srli_3; unorm; reflexivity).                                (* [comment removed for export] *)
      av Fo776 D_5a148 (Z_to_bv 64 (b + s) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).               (* [comment removed for export] *)
      av Fo780 D_5a14c (Z_to_bv 64 (zshad b) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, zshad in G in change_no_check G' end); unorm; f_equal; lia).     (* [comment removed for export] *)
      av Fo784 D_5a150 (Z_to_bv 64 (b + s - 8) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).         (* [comment removed for export] *)
      av Fo788 D_5a154 (Z_to_bv 64 ((b + s - 8) / 8) : word) ltac:(rewrite v_srli_3; unorm; reflexivity).                      (* [comment removed for export] *)
      cldc Fo792 D_5a158 (pt_p_cfl pt + 120)%Z (Z_to_bv 64 thr : word) ltac:(rd_peel MO Rthr).                  (* [comment removed for export] *)
      pose proof (Z.div_pos (b + s - 8) 8 ltac:(lia) ltac:(lia)) as Hq1.
      pose proof (Z.div_le_mono (b + s - 8) 0x7fff8000 8 ltac:(lia) ltac:(lia)) as Hq2.
      replace (0x7fff8000 / 8)%Z with 0xffff000%Z in Hq2 by reflexivity.
      av Fo796 D_5a15c (Z_to_bv 64 (0x7fff8000 + (b + s - 8) / 8) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).  (* [comment removed for export] *)
      av Fo800 D_5a160 (Z_to_bv 64 (zshad b + s / 8) : word)
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi, zshad in G in change_no_check G' end); unorm; f_equal; pose proof (shadow_end_eq b s Hb Hb8 Hs8 Hs); lia).   (* [comment removed for export] *)
      av Fo804 D_5a164 (Z_to_bv 64 (s / 8) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub, zshad in G in change_no_check G' end); unorm; f_equal; lia).     (* [comment removed for export] *)
      ab_tk Fo808 D_5a168 ltac:(condz).                 (* [comment removed for export] *)
      cldc Fo408 D_59fd8 (pt_p_rms pt) (pt_mset pt) ltac:(rd_peel MO Rrms).                                              (* [comment removed for export] *)
      an Fo412 D_59fdc.                                  (* [comment removed for export] *)
      aret Fo416 D_59fe0 (pt_mset pt).                  (* [comment removed for export] *)
      replace (at_ (pt_mset pt) 0) with (pt_mset pt) by (symmetry; apply at_0). wd_refl.
    - post.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma ug_iterB : forall (M : word -> option byte) r0 (i : nat) (b s k : Z),
    memI M -> nth_error globs i = Some (b, s) -> (0 <= k)%Z -> (k + 1 <= N)%Z ->
    getr r0 2 = at_ sp (-208) -> getr r0 18 = Z_to_bv 64 2 ->
    getr r0 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat i) -> getr r0 27 = Z_to_bv 64 (k + 1) ->
    exists r,
      msteps segs (mkst r0 (at_ base 420) M rom) (mkst r (at_ base 440) M rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat (S i)) /\ getr r 27 = Z_to_bv 64 k
      /\ (forall x : reg, In x [8; 9; 18; 19; 21; 22; 23; 24; 25; 26]%list -> getr r x = getr r0 x)
      /\ regs_agree CLX r0 r.
  Proof using HG Hps_mu Hps Hmu Hcells Hsp thr HCODE c_ro c_inited g_pgsz p_aflags g_aflags p_flag g_stop g_start pt dbase.
    intros M r0 i b s k [MO MG] Hi Hk HkN Q2 Q18 Q20 Q27.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. cells_split.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    destruct (HG i b s Hi) as (Rb & Rs & Rodr & Hb & Hb8 & Hs8 & Hs & Hbs & Hsthr & STb).
    pose proof (nth_lt _ _ _ Hi) as Hilen. apply Nat2Z.inj_lt in Hilen.
    wd_eexists. split.
    - cldc Fo420 D_59fe4 (p_start + 64 * Z.of_nat i + 56)%Z (Z_to_bv 64 (2 ^ 64 - 1) : word) ltac:(rd_peel MO Rodr).  (* [comment removed for export] *)
      an Fo424 D_59fe8.                                  (* [comment removed for export] *)
      ab_ft Fo428 D_59fec ltac:(condz).                 (* [comment removed for export] *)
      av Fo432 D_59ff0 (Z_to_bv 64 k : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).                           (* [comment removed for export] *)
      av Fo436 D_59ff4 (Z_to_bv 64 (p_start + 64 * Z.of_nat (S i)) : word) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia). (* [comment removed for export] *)
      wd_refl.
    - post.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma ug_iter : forall (M : word -> option byte) r0 (i : nat) (b s k : Z),
    memI M -> nth_error globs i = Some (b, s) -> (0 <= k)%Z -> (k + 1 <= N)%Z ->
    getr r0 2 = at_ sp (-208) -> getr r0 9 = Z_to_bv 64 p_cfl -> getr r0 18 = Z_to_bv 64 2 ->
    getr r0 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat i) -> getr r0 23 = Z_to_bv 64 p_rms ->
    getr r0 25 = Z_to_bv 64 p_aflags -> getr r0 26 = Z_to_bv 64 p_shoff -> getr r0 27 = Z_to_bv 64 (k + 1) ->
    exists r,
      msteps segs (mkst r0 (at_ base 444) M rom) (mkst r (at_ base 440) (shz M [(b, s)]) rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat (S i)) /\ getr r 27 = Z_to_bv 64 k
      /\ (forall x : reg, In x [9; 18; 19; 21; 22; 23; 24; 25; 26]%list -> getr r x = getr r0 x)
      /\ regs_agree CLX r0 r.
  Proof using Hmset_ok HG Hps_mu Hps Hmu Hcells_mu Hcells Hthr Rthr Rrms Rsh Hcpm Rcpm Rini Rrg Hsp thr cpm Hbase HCPM HAI PTOK HCODE c_ro c_inited g_pgsz g_aflags p_flag g_stop g_start dbase.
    intros M r0 i b s k MI Hi Hk HkN Q2 Q9 Q18 Q20 Q23 Q25 Q26 Q27.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    destruct Hps as (P0 & P8 & Pend & PN).
    destruct (HG i b s Hi) as (Rb & Rs & Rodr & Hb & Hb8 & Hs8 & Hs & Hbs & Hsthr & STb).
    pose proof (Z.div_mod b 8 ltac:(lia)) as Hbq. pose proof (Z.div_mod s 8 ltac:(lia)) as Hsq.
    pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)) as Hbq0. pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)) as Hsq0.
    pose proof (Z.div_le_mono (b + s) 0x7fff8000 8 ltac:(lia) ltac:(lia)) as Hq2.
    replace (0x7fff8000 / 8)%Z with 0xffff000%Z in Hq2 by reflexivity.
    replace ((b + s) / 8)%Z with (b / 8 + s / 8)%Z in Hq2
      by (replace (b + s)%Z with ((b / 8 + s / 8) * 8)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
    destruct (ug_iterA M r0 i b s MI Hi Q2 Q9 Q18 Q20 Q23 Q25 Q26) as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & AK & AG1).
    destruct MI as [MO MG].
    destruct (memset_summary segs mset (pto_mset _ _ PTOK) M (Z_to_bv 64 (zshad b)) (Z_to_bv 64 0) (at_ base 420) (s / 8) rom
                ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold zshad in G in change_no_check G' end); wd_ulia)
                ltac:(eapply store_ok_mono; [exact MG | exact STb])
                ltac:(apply ret_ok_at; [lia | reflexivity | lia])
                r1 A10 A11 A12 A1) as (r2 & RUN2 & B10 & AG2).
    assert (MI' : memI (shz M [(b, s)])) by (apply memI_shz1; [split; assumption | lia | exact Hb8 | lia | lia]).
    assert (B2 : getr r2 2 = at_ sp (-208)) by (rewrite (AG2 2) by notin; exact A2).
    assert (B18 : getr r2 18 = Z_to_bv 64 2) by (rewrite (AG2 18) by notin; rewrite (AK 18) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q18).
    assert (B20 : getr r2 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat i)) by (rewrite (AG2 20) by notin; rewrite (AK 20) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q20).
    assert (B27 : getr r2 27 = Z_to_bv 64 (k + 1)) by (rewrite (AG2 27) by notin; rewrite (AK 27) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q27).
    destruct (ug_iterB (shz M [(b, s)]) r2 i b s k MI' Hi Hk HkN B2 B18 B20 B27) as (r3 & RUN3 & C2 & C20 & C27 & CK & AG3).
    exists r3. split; [|split; [exact C2 | split; [exact C20 | split; [exact C27 | split]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. (lazymatch goal with |- ?G => let G' := eval cbn [shz] in G in change_no_check G' end). exact RUN3.
    - intros x Hx. rewrite (CK x) by (clear - Hx; cbn [In] in Hx |- *; am_tauto). rewrite (AG2 x) by (clear - Hx; cbn [In] in Hx; (lazymatch goal with |- ?G => let G' := eval unfold ms_clob in G in change_no_check G' end); intros Hin; cbn [In] in Hin; intuition (subst; discriminate)).
      apply AK. clear - Hx. cbn [In] in Hx |- *. am_tauto.
    - intros x Hx. rewrite (AG3 x Hx). rewrite (AG2 x). 2:{ intros Hin. apply Hx. clear - Hin. unfold ms_clob in Hin. cbn [In] in Hin |- *. intuition (subst; am_tauto). }
      exact (AG1 x Hx).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma memI_UMC : memI UMC.
  Proof using Hmu Hsp. split; [exact UMC_o3 | exact UMC_grows]. Qed.

  Lemma memI_shz : forall l M, memI M ->
    Forall (fun bs => 0 <= fst bs /\ fst bs mod 8 = 0 /\ fst bs + snd bs <= 0x7fff8000 /\ 8 <= snd bs)%Z l ->
    memI (shz M l).
  Proof using Hps Hmu thr globs p_start dbase base.
    induction l as [|[b s] l IH]; intros M MI Hl; [exact MI|].
    apply Forall_cons_iff in Hl as [[Hb [Hb8 [Hbs Hs]]] Hl]. cbn [fst snd] in Hb, Hb8, Hbs, Hs.
    change (shz M ((b, s) :: l)) with (shz (shz M [(b, s)]) l). apply IH; [|exact Hl]. apply memI_shz1; [exact MI | lia | exact Hb8 | lia | lia].
  Qed.

  Lemma ug_loop : forall todo done r0,
    globs = done ++ todo -> todo <> [] ->
    getr r0 2 = at_ sp (-208) -> getr r0 9 = Z_to_bv 64 p_cfl -> getr r0 18 = Z_to_bv 64 2 ->
    getr r0 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat (length done)) -> getr r0 23 = Z_to_bv 64 p_rms ->
    getr r0 25 = Z_to_bv 64 p_aflags -> getr r0 26 = Z_to_bv 64 p_shoff -> getr r0 27 = Z_to_bv 64 (Z.of_nat (length todo)) ->
    exists r,
      msteps segs (mkst r0 (at_ base 444) (shz UMC done) rom) (mkst r (at_ base 960) (shz UMC globs) rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 20 = Z_to_bv 64 (p_start + 64 * N)
      /\ (forall x : reg, In x [9; 18; 19; 21; 22; 23; 24; 25; 26]%list -> getr r x = getr r0 x)
      /\ regs_agree CLX r0 r.
  Proof using Hmset_ok HG Hps_mu Hps Hmu Hcells_mu Hcells Hthr Rthr Rrms Rsh Hcpm Rcpm Rini Rrg Hsp thr cpm Hbase HCPM HAI PTOK HCODE c_ro c_inited g_pgsz g_aflags g_stop g_start.
    induction todo as [|[b s] rest IH]; intros done r0 Hg Hne Q2 Q9 Q18 Q20 Q23 Q25 Q26 Q27; [exfalso; apply Hne; reflexivity|].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    destruct Hps as (P0 & P8 & Pend & PN).
    assert (HL : (Z.of_nat (length done) + Z.of_nat (length rest) + 1 = N)%Z).
    { rewrite Hg, length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia. }
    assert (Hi : nth_error globs (length done) = Some (b, s)).
    { rewrite Hg, nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    assert (MI : memI (shz UMC done)).
    { apply memI_shz; [exact memI_UMC|]. pose proof globs_ok as GO. rewrite Hg in GO. apply Forall_app in GO as [GO _]. exact GO. }
    cbn [length] in Q27. rewrite Nat2Z.inj_succ, <- Z.add_1_r in Q27.
    destruct (ug_iter (shz UMC done) r0 (length done) b s (Z.of_nat (length rest)) MI Hi ltac:(lia) ltac:(lia)
                Q2 Q9 Q18 Q20 Q23 Q25 Q26 Q27) as (r1 & RUN1 & A2 & A20 & A27 & AK & AG1).
    rewrite <- shz_app in RUN1.
    destruct rest as [|g rest']; cbn [length] in A27, HL.
    - (* [comment removed for export] *)
      wd_eexists. split; [|split; [|split; [|split]]].
      + eapply msteps_trans; [exact RUN1|].
        replace (done ++ [(b, s)]) with globs by (rewrite Hg; reflexivity).
        ab_tk Fo440 D_59ff8 ltac:(condz).
        wd_refl.
      + exact A2.
      + rewrite A20. f_equal. lia.
      + exact AK.
      + exact AG1.
    - (* [comment removed for export] *)
      assert (A9 : getr r1 9 = Z_to_bv 64 p_cfl) by (rewrite (AK 9) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q9).
      assert (A18 : getr r1 18 = Z_to_bv 64 2) by (rewrite (AK 18) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q18).
      assert (A23 : getr r1 23 = Z_to_bv 64 p_rms) by (rewrite (AK 23) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q23).
      assert (A25 : getr r1 25 = Z_to_bv 64 p_aflags) by (rewrite (AK 25) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q25).
      assert (A26 : getr r1 26 = Z_to_bv 64 p_shoff) by (rewrite (AK 26) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact Q26).
      assert (A20' : getr r1 20 = Z_to_bv 64 (p_start + 64 * Z.of_nat (length (done ++ [(b, s)])))).
      { rewrite A20, length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). f_equal. lia. }
      assert (A27' : getr r1 27 = Z_to_bv 64 (Z.of_nat (length (g :: rest')))) by exact A27.
      destruct (IH (done ++ [(b, s)]) r1 ltac:(rewrite Hg, <- app_assoc; reflexivity) ltac:(intros X; discriminate X)
                  A2 A9 A18 A20' A23 A25 A26 A27') as (r2 & RUN2 & B2 & B20 & BK & AG2).
      exists r2. split; [|split; [exact B2 | split; [exact B20 | split]]].
      + eapply msteps_trans; [exact RUN1|].
        ab_ft Fo440 D_59ff8 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); unorm; condz).
        exact RUN2.
      + intros x Hx. rewrite (BK x Hx). exact (AK x Hx).
      + intros x Hx. rewrite (AG2 x Hx). exact (AG1 x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma ug_loop_all : forall r0,
    getr r0 2 = at_ sp (-208) -> getr r0 9 = Z_to_bv 64 p_cfl -> getr r0 18 = Z_to_bv 64 2 ->
    getr r0 20 = Z_to_bv 64 p_start -> getr r0 23 = Z_to_bv 64 p_rms ->
    getr r0 25 = Z_to_bv 64 p_aflags -> getr r0 26 = Z_to_bv 64 p_shoff -> getr r0 27 = Z_to_bv 64 N ->
    exists r,
      msteps segs (mkst r0 (at_ base 444) UMC rom) (mkst r (at_ base 960) UMD rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 20 = Z_to_bv 64 (p_start + 64 * N)
      /\ (forall x : reg, In x [9; 18; 19; 21; 22; 23; 24; 25; 26]%list -> getr r x = getr r0 x)
      /\ regs_agree CLX r0 r.
  Proof using Hmset_ok HG Hps_mu Hps HN Hmu Hcells_mu Hcells Hthr Rthr Rrms Rsh Hcpm Rcpm Rini Rrg Hsp thr cpm Hbase HCPM HAI PTOK HCODE c_ro c_inited g_pgsz g_aflags g_stop g_start.
    intros r0 Q2 Q9 Q18 Q20 Q23 Q25 Q26 Q27.
    apply (ug_loop globs [] r0 eq_refl).
    - intros E. rewrite E in HN. cbn in HN. lia.
    - exact Q2. - exact Q9. - exact Q18.
    - rewrite Q20. f_equal. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    - exact Q23. - exact Q25. - exact Q26. - exact Q27.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma UMD_rd_frame : forall (a : word) k bs,
    (U sp - 272 <= U a)%Z -> (U a + Z.of_nat k <= U sp)%Z ->
    rdn segs UMC a k = Some bs -> rdn segs UMD a k = Some bs.
  Proof using HG Hps Hmu Hsp thr.
    intros a k bs H1 H2 Hr. pose proof (u64_range sp). rewrite <- Hr. (lazymatch goal with |- ?G => let G' := eval unfold UMD in G in change_no_check G' end). apply rdn_ext; [lia|].
    intros x Hx. apply (shz_out globs UMC x globs_ok). lia.
  Qed.

  Lemma shad_z : forall z, (0 <= z < 2 ^ 64)%Z -> shad (Z_to_bv 64 z) = zshad z.
  Proof using globs p_mu p_start dbase base. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold shad, zshad in G in change_no_check G' end). unorm. reflexivity. Qed.
  Lemma shlen_64N : shlen (Z_to_bv 64 (64 * N)) = (8 * N)%Z.
  Proof using Hps_mu Hps HN Hmu thr p_mu p_start dbase base.
    destruct Hps as (P0 & P8 & Pend & PN). (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm.
    replace (64 * N)%Z with (8 * N * 8)%Z by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.

  Lemma blkU3 : forall r0,
    getr r0 2 = at_ sp (-208) -> getr r0 18 = Z_to_bv 64 2 -> getr r0 19 = v_str ->
    getr r0 20 = Z_to_bv 64 (p_start + 64 * N) -> getr r0 21 = Z_to_bv 64 2305843009213693952 -> getr r0 24 = Z_to_bv 64 p_mu ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 960) UMD rom) (mkst r (at_ base 988) UME rom)
      /\ getr r 2 = at_ sp (-208) /\ getr r 8 = Z_to_bv 64 2305843009213693952 /\ getr r 9 = Z_to_bv 64 1
      /\ getr r 24 = Z_to_bv 64 p_mu
      /\ regs_agree CLX regs r.
  Proof using Hmset_nz Hmset_ok Hshd Hstk HG Hps_mu Hps HN Hmu Hcells_mu Hcells Hthr Rthr Rgcf Rrms Rgrms Rhe Rghe Rme Rgme Rmb Rgmb Rsh Rgsh Hsp thr midend cpm Hbase PTB PTOK HCODE c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start.
    intros r0 Q2 Q18 Q19 Q20 Q21 Q24 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    (* [comment removed for export] *)
    set (rc := regupd (regupd (regupd (regupd (regupd (regupd (regupd r0
                 9 (Z_to_bv 64 1)) 8 (Z_to_bv 64 2305843009213693952)) 11 (Z_to_bv 64 N)) 11 (Z_to_bv 64 (64 * N)))
                 10 (Z_to_bv 64 p_start)) 12 (Z_to_bv 64 0)) 1 (at_ base 988)).
    assert (PH : poisonH segs pt UMD (Z_to_bv 64 p_start) (Z_to_bv 64 (64 * N)) (Z_to_bv 64 0) (at_ base 988) (at_ sp (-208)) cpm midend thr).
    { cells_split. split.
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rgsh].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rsh].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rgmb].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rmb].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rgme].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rme].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rghe].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rhe].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rgrms].
      - apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rrms].
      - exact Hmset_nz.
      - exact Hmset_ok.
      - intros C. exfalso. apply C. reflexivity.
      - intros _. split; [|split; [|split; [rewrite shlen_64N; lia | exact Hthr]]].
        + apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rgcf].
        + apply (rd_cell _ _ _ _ UMD_out); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rthr].
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). rewrite at_u by lia. repeat apply Forall_cons; try apply Forall_nil; lia.
      - unorm. exact P8.
      - unorm. replace (64 * N)%Z with (8 * N * 8)%Z by lia. apply Z.mod_mul. lia.
      - right. unorm. lia.
      - rewrite at_u by lia. lia.
      - rewrite at_at. eapply store_ok_mono; [apply UMD_grows|].
        eapply (store_ok_sub segs mem (at_ sp (-272)) _ 272); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite shad_z by lia. rewrite shlen_64N. eapply store_ok_mono; [apply UMD_grows | exact Hshd].
      - apply ret_ok_at; [lia | reflexivity | lia]. }
    destruct (poison_shadow segs pt PTOK UMD rom _ _ _ _ _ cpm midend thr rc PH) as (rP & RUNP & AGP).
    1-5: subst rc; gres; try reflexivity. 1: exact Q2.
    rewrite PTB in RUNP.
    wd_eexists. split.
    - an Fo960 D_5a200.                                  (* [comment removed for export] *)
      an Fo964 D_5a204.                                  (* [comment removed for export] *)
      fld Fo968 D_5a208 (Z_to_bv 64 N : word) ltac:(apply UMD_rd_frame; [rewrite at_u; lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]; (lazymatch goal with |- ?G => let G' := eval unfold UMC in G in change_no_check G' end)).  (* [comment removed for export] *)
      av Fo972 D_5a20c (Z_to_bv 64 (64 * N) : word) ltac:(rewrite v_slli_mul by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
      fld Fo976 D_5a210 (Z_to_bv 64 p_start : word) ltac:(apply UMD_rd_frame; [rewrite at_u; lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]; (lazymatch goal with |- ?G => let G' := eval unfold UMC, UMB, UM3 in G in change_no_check G' end)).  (* [comment removed for export] *)
      an Fo980 D_5a214.                                  (* [comment removed for export] *)
      an Fo984 D_5a218.                                  (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst ?r _ _ _) _ => change r with rc end.
      eapply msteps_trans; [exact RUNP|].
      subst rc. gres. rewrite Q18, Q19, Q20, Q21. rewrite shad_z by lia. rewrite shlen_64N.
      change (wbytes (ps_frame UMD _ _ _ _ _ _ _ _) _ _) with UME.
      wd_refl.
    - split; [|split; [|split; [|split]]].
      + rewrite (AGP 2) by notin. subst rc; gres. exact Q2.
      + rewrite (AGP 8) by notin. subst rc; gres. reflexivity.
      + rewrite (AGP 9) by notin. subst rc; gres. reflexivity.
      + rewrite (AGP 24) by notin. subst rc; gres. exact Q24.
      + intros x Hx. rewrite (AGP x). 2:{ intros Hin. apply Hx. revert Hin. generalize x. (lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end). incl_lists. }
        subst rc. destruct (decide (x = 1)) as [->|N1]; [exfalso; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto|].
        destruct (decide (x = 12)) as [->|N12]; [exfalso; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto|].
        destruct (decide (x = 10)) as [->|N10]; [exfalso; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto|].
        destruct (decide (x = 11)) as [->|N11]; [exfalso; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto|].
        destruct (decide (x = 8)) as [->|N8]; [exfalso; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto|].
        destruct (decide (x = 9)) as [->|N9]; [exfalso; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto|].
        rewrite !getr_other by assumption. exact (AG0 x Hx).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zshad_ps : (0x7fff8000 <= zshad p_start)%Z /\ (zshad p_start + 8 * N <= 0x8fff8000)%Z.
  Proof using Hps Hmu thr p_mu dbase base.
    destruct Hps as (P0 & P8 & Pend & PN). (lazymatch goal with |- ?G => let G' := eval unfold zshad in G in change_no_check G' end).
    pose proof (Z.div_mod p_start 8 ltac:(lia)). pose proof (Z.div_pos p_start 8 ltac:(lia) ltac:(lia)). lia.
  Qed.
  Lemma UME_grows : mem_grows mem UME.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UME, ps_frame in G in change_no_check G' end). eapply mem_grows_trans; [apply UMD_grows|]. grows_tac. Qed.
  Lemma UMF_grows : mem_grows mem UMF.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UMF in G in change_no_check G' end). eapply mem_grows_trans; [apply UME_grows|]. grows_tac. Qed.
  Lemma UME_o3 : forall x : word, (U x < U sp - 272 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UME x = mem x.
  Proof using HG Hps HN Hmu Hsp thr segs.
    intros x Hx Hm Hs. pose proof (u64_range sp). pose proof zshad_ps as [Z1 Z2]. destruct Hps as (P0 & P8 & Pend & PN).
    (lazymatch goal with |- ?G => let G' := eval unfold UME, ps_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; [apply UMD_out; lia | ..];
      (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_at, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia.
  Qed.
  Lemma rd_cell2 : forall (M : word -> option byte) (c : Z) k bs,
    (forall x : word, (U x < U sp - 272 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z ->
                      (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= 0x7fff8000)%Z -> (c + Z.of_nat k <= p_mu \/ p_mu + 8 <= c)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs -> rdn segs M (Z_to_bv 64 c) k = Some bs.
  Proof using Hps Hmu Hsp thr globs p_start dbase base.
    intros M c k bs HM Hc Hk Hm Hr. pose proof (u64_range sp). rewrite <- Hr. apply rdn_ext; [wd_ulia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply HM; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma UME_rd_frame : forall (a : word) k bs,
    (U sp - 208 <= U a)%Z -> (U a + Z.of_nat k <= U sp)%Z ->
    rdn segs UMC a k = Some bs -> rdn segs UME a k = Some bs.
  Proof using HG Hps HN Hmu Hsp thr.
    intros a k bs H1 H2 Hr. pose proof (u64_range sp). pose proof zshad_ps as [Z1 Z2]. destruct Hps as (P0 & P8 & Pend & PN).
    (lazymatch goal with |- ?G => let G' := eval unfold UME, ps_frame in G in change_no_check G' end).
    rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; [apply UMD_rd_frame; [lia | exact H2 | exact Hr] | ..];
      rewrite ?at_at, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia.
  Qed.
  Lemma UMF_rd_frame : forall (a : word) k bs,
    (U sp - 208 <= U a)%Z -> (U a + Z.of_nat k <= U sp)%Z ->
    rdn segs UMC a k = Some bs -> rdn segs UMF a k = Some bs.
  Proof using HG Hps HN Hmu Hsp thr.
    intros a k bs H1 H2 Hr. pose proof (u64_range sp). destruct Hmu as (M0 & M8 & Mal). (lazymatch goal with |- ?G => let G' := eval unfold UMF in G in change_no_check G' end).
    rewrite rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply UME_rd_frame; assumption | wd_ulia | lia | wd_ulia].
  Qed.
  (* [comment removed for export] *)
  Lemma UMC_rd_hi : forall (a : word) bs,
    (U sp - 136 <= U a)%Z -> (U a + 8 <= U sp)%Z ->
    rdn segs UM3 a 8 = Some bs -> rdn segs UMC a 8 = Some bs.
  Proof using Hps Hmu Hsp thr.
    intros a bs H1 H2 Hr. pose proof (u64_range sp). destruct Hmu as (M0 & M8 & Mal). (lazymatch goal with |- ?G => let G' := eval unfold UMC, UMB in G in change_no_check G' end).
    rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes; [exact Hr | ..];
      rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia.
  Qed.
  (* [comment removed for export] *)
  Lemma rdn_shz_off : forall l M (a : word) k,
    Forall (fun bs => 0 <= fst bs /\ fst bs mod 8 = 0 /\ fst bs + snd bs <= 0x7fff8000 /\ 8 <= snd bs)%Z l ->
    (U a + Z.of_nat k <= 0x7fff8000)%Z -> rdn segs (shz M l) a k = rdn segs M a k.
  Proof using Hps Hmu thr globs p_mu p_start dbase base.
    intros l M a k Hl Ha. apply rdn_ext; [lia|]. intros x Hx. apply (shz_out l M x Hl). lia.
  Qed.
  Lemma UME_mu : rdn segs UME (Z_to_bv 64 p_mu) 8 = Some (LE8z 1152921504606846976).
  Proof using HG Hps HN Hmu Hsp thr.
    pose proof (u64_range sp) as Hspr. pose proof zshad_ps as [Z1 Z2]. destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    (lazymatch goal with |- ?G => let G' := eval unfold UME, ps_frame in G in change_no_check G' end).
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]).
    (lazymatch goal with |- ?G => let G' := eval unfold UMD in G in change_no_check G' end). rewrite (rdn_shz_off globs UMC _ 8 globs_ok) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia).
    (lazymatch goal with |- ?G => let G' := eval unfold UMC, UMB in G in change_no_check G' end). rd8_chain.
  Qed.

  Definition unreg_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac spctx := match goal with Hr' : (0 <= bv_unsigned sp < 2 ^ 64)%Z |- _ => clear - Hr' Hsp end.
  Ltac rd8_chainP :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | spctx; rd8_side ]);
    apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac fldF F D d vv :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
          lazymatch goal with |- rdn _ ?M ?a _ = _ => replace a with (at_ sp d) by (rewrite ?at_at; first [reflexivity | f_equal; lia]) end;
          lazymatch goal with
          | |- rdn _ UMG _ _ = _ => (lazymatch goal with |- ?G => let G' := eval unfold UMG in G in change_no_check G' end); rewrite wd_rdn_wbytes_out3; wd_lenlit; rewrite ?length_N_to_le_bytes; [ | rd8_side ]
          | |- _ => idtac
          end;
          apply UMF_rd_frame; [spctx; rewrite at_u; lia | spctx; rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia |];
          apply UMC_rd_hi; [spctx; rewrite at_u; lia | spctx; rewrite at_u; lia |];
          (lazymatch goal with |- ?G => let G' := eval unfold UM3, UM2, UM1 in G in change_no_check G' end); rd8_chainP
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Lemma blkU4 : forall r0,
    getr r0 2 = at_ sp (-208) -> getr r0 8 = Z_to_bv 64 2305843009213693952 -> getr r0 9 = Z_to_bv 64 1 ->
    getr r0 24 = Z_to_bv 64 p_mu -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 988) UME rom) (mkst r ra UMG rom)
      /\ regs_agree (fun x => In x unreg_clob) regs r.
  Proof using Hfl_ok Hmu_ok HG Hps HN Hmu Hcells_mu Hcells Rro Hret R2 R1 Hsp ro thr Hdbase Hbase G1008 DCODE HCODE c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start.
    intros r0 Q2 Q8 Q9 Q24 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dbase) as Hdr.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal). cells_split.
    destruct G1008 as (x1008 & G1008a & G1008b).
    assert (RETE : ret_ok (at_ base 1648)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (RETD : ret_ok (at_ dbase 36)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8z (p_mu - 64)) (v := Z_to_bv 64 (p_mu - 64));
          [exact Fo988 | reflexivity | exact D_5a21c
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            apply UME_rd_frame; [rewrite at_u; lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; (lazymatch goal with |- ?G => let G' := eval unfold UMC in G in change_no_check G' end); rd8_chain
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      cldc Fo992 D_5a220 p_mu (Z_to_bv 64 1152921504606846976 : word) ltac:(exact UME_mu).   (* [comment removed for export] *)
      an Fo996 D_5a224.                                  (* [comment removed for export] *)
      an Fo1000 D_5a228.                                 (* [comment removed for export] *)
      an Fo1004 D_5a22c.                                 (* [comment removed for export] *)
      eapply msteps_trans; [apply G1008a|]. zlit_at.     (* [comment removed for export] *)
      an Fo1012 D_5a234.                                 (* [comment removed for export] *)
      an Fo1016 D_5a238.                                 (* [comment removed for export] *)
      an Fo1020 D_5a23c.                                 (* [comment removed for export] *)
      eapply msteps_trans; [eapply G1008b; [gres; reflexivity | apply (rd_cell2 _ _ _ _ UME_o3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | mu_off | exact Rro]]|]. zlit_at.  (* [comment removed for export] *)
      an Fo1028 D_5a244.                                 (* [comment removed for export] *)
      an Fo1032 D_5a248.                                 (* [comment removed for export] *)
      an Fo1036 D_5a24c.                                 (* [comment removed for export] *)
      an Fo1040 D_5a250.                                 (* [comment removed for export] *)
      an Fo1044 D_5a254.                                 (* [comment removed for export] *)
      an Fo1072 D_5a270.                                 (* [comment removed for export] *)
      an Fo1076 D_5a274.                                 (* [comment removed for export] *)
      ab_ft Fo1080 D_5a278 ltac:(condz).                (* [comment removed for export] *)
      an Fo1084 D_5a27c.                                 (* [comment removed for export] *)
      ab_tk Fo1088 D_5a280 ltac:(condz).                (* [comment removed for export] *)
      an Fo1124 D_5a2a4.                                 (* [comment removed for export] *)
      an Fo1128 D_5a2a8.                                 (* [comment removed for export] *)
      an Fo1132 D_5a2ac.                                 (* [comment removed for export] *)
      an Fo1136 D_5a2b0.                                 (* [comment removed for export] *)
      an Fo1140 D_5a2b4.                                 (* [comment removed for export] *)
      an Fo1144 D_5a2b8.                                 (* [comment removed for export] *)
      an Fo1148 D_5a2bc.                                 (* [comment removed for export] *)
      ab_tk Fo1152 D_5a2c0 ltac:(condz).                (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run segs _ (at_ base 1048) (at_ base 1052) (at_ base 1056) (at_ base 1060) (at_ base 1064) UME rom
                  _ _ _ _ _ _ _ _ 6 24 7 5 6 10 BC_NE _ _ (LE8z 1152921504606846976) (Z_to_bv 64 1152921504606846976)
                  Fo1048 eq_refl D_5a258 Fo1052 eq_refl D_5a25c Fo1056 eq_refl D_5a260 Fo1060 eq_refl D_5a264);
          rewrite ?at_addi; try reflexivity.
        all: lazymatch goal with
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rewrite Q24; unorm; exact Mal
             | |- rdn _ _ _ _ = _ => gres; rewrite Q24; exact UME_mu
             | |- store_ok _ _ _ _ = true => gres; rewrite Q24; eapply store_ok_mono; [apply UME_grows | exact Hmu_ok]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rewrite Q24.
      change (wbytes UME (Z_to_bv 64 p_mu) (LE8 (Z_to_bv 64 0))) with UMF.
      ab_tk Fo1064 D_5a268 ltac:(condz).                (* [comment removed for export] *)
      ab_ft Fo1168 D_5a2d0 ltac:(condz).                (* [comment removed for export] *)
      fldF Fo1172 D_5a2d4 (-40)%Z (at_ base 1648).        (* [comment removed for export] *)
      fldF Fo1176 D_5a2d8 (-48)%Z (Z_to_bv 64 p_flag : word).   (* [comment removed for export] *)
      fldF Fo1180 D_5a2dc (-56)%Z (getr regs 9).          (* [comment removed for export] *)
      fldF Fo1184 D_5a2e0 (-64)%Z (getr regs 18).         (* [comment removed for export] *)
      fldF Fo1188 D_5a2e4 (-72)%Z (getr regs 19).         (* [comment removed for export] *)
      fldF Fo1192 D_5a2e8 (-80)%Z (getr regs 20).         (* [comment removed for export] *)
      fldF Fo1196 D_5a2ec (-88)%Z (getr regs 21).         (* [comment removed for export] *)
      fldF Fo1200 D_5a2f0 (-96)%Z (getr regs 22).         (* [comment removed for export] *)
      fldF Fo1204 D_5a2f4 (-104)%Z (getr regs 23).        (* [comment removed for export] *)
      fldF Fo1208 D_5a2f8 (-112)%Z (getr regs 24).        (* [comment removed for export] *)
      fldF Fo1212 D_5a2fc (-120)%Z (getr regs 25).        (* [comment removed for export] *)
      fldF Fo1216 D_5a300 (-128)%Z (getr regs 26).        (* [comment removed for export] *)
      fldF Fo1220 D_5a304 (-136)%Z (getr regs 27).        (* [comment removed for export] *)
      an Fo1224 D_5a308.                                 (* [comment removed for export] *)
      aret Fo1228 D_5a30c (at_ base 1648).               (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := (Z_to_bv 64 p_flag : word));
          [exact Fo1648 | reflexivity | exact D_5a4b0
          | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity
          | gres; reflexivity
          | eapply store_ok_mono; [apply UMF_grows | exact Hfl_ok] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes UMF _ _) with UMG.
      fldF Fo1652 D_5a4b4 (-24)%Z (at_ dbase 36).          (* [comment removed for export] *)
      fldF Fo1656 D_5a4b8 (-32)%Z (getr regs 8).           (* [comment removed for export] *)
      an Fo1660 D_5a4bc.                                 (* [comment removed for export] *)
      aret Fo1664 D_5a4c0 (at_ dbase 36).                (* [comment removed for export] *)
      fldF Do36 D_bf044 (-8)%Z ra.                        (* [comment removed for export] *)
      an Do40 D_bf048.                                  (* [comment removed for export] *)
      aret Do44 D_bf04c ra.                             (* [comment removed for export] *)
      wd_refl.
    - apply (regs_agree_strengthen unreg_clob [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list).
      + ra_solve.
      + intros x Hx Hn. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx]; [first [gres; rwH; rewrite ?at_0; reflexivity | exfalso; apply Hn; (lazymatch goal with |- ?G => let G' := eval unfold unreg_clob in G in change_no_check G' end); clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto] |]).
        destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem unreg_run :
    exists r,
      msteps segs (mkst regs (at_ dbase 0) mem rom) (mkst r ra UMG rom)
      /\ regs_agree (fun x => In x unreg_clob) regs r.
  Proof using Hmset_nz Hmset_ok Hshd Hfl_ok Hmu_ok Hstk HG Hps_mu Hps HN Hmu Hcells_mu Hcells Rro Rpg Hthr Rthr Rgcf Rrms Rgrms Rhe Rghe Rme Rgme Rmb Rgmb Rsh Rgsh Hcpm Rcpm Rini Rmu Rrg Rga Hfl Rfl Rge Rgs Hret R2 R1 Hsp ro thr midend cpm vflag Hdbase Hbase DJ32 DG24 DG12 DG8 G1008 G388 G336 G332 G328 G324 G320 G316 G312 G84 G60 HCPM HAI PTB PTOK DCODE HCODE c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start.
    destruct blkDE as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A14 & AK & AG1).
    destruct (blkU1 r1 A1 A2 A8 A10 A11 AK AG1) as (r2 & RUN2 & B2 & B12 & B13 & B14 & B21 & B22 & B23 & B24 & B25 & AG2).
    destruct (blkU2 r2 B2 B12 B13 B14 B21 B22 B23 B24 B25 AG2)
      as (r3 & RUN3 & C2 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & AG3).
    destruct (ug_loop_all r3 C2 C9 C18 C20 C23 C25 C26 C27) as (r4 & RUN4 & D2 & D20 & DK & AG4).
    assert (D18 : getr r4 18 = Z_to_bv 64 2) by (rewrite (DK 18) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact C18).
    assert (D19 : getr r4 19 = v_str) by (rewrite (DK 19) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact C19).
    assert (D21 : getr r4 21 = Z_to_bv 64 2305843009213693952) by (rewrite (DK 21) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact C21).
    assert (D24 : getr r4 24 = Z_to_bv 64 p_mu) by (rewrite (DK 24) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto); exact C24).
    assert (AG4' : regs_agree CLX regs r4) by (intros x Hx; rewrite (AG4 x Hx); exact (AG3 x Hx)).
    destruct (blkU3 r4 D2 D18 D19 D20 D21 D24 AG4') as (r5 & RUN5 & E2 & E8 & E9 & E24 & AG5).
    destruct (blkU4 r5 E2 E8 E9 E24 AG5) as (r6 & RUN6 & AG6).
    exists r6. split; [|exact AG6].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

  (* [comment removed for export] *)
  Theorem UMG_outside : forall x : word,
    (U x < U sp - 272 \/ U sp <= U x)%Z -> (U x < p_mu \/ p_mu + 8 <= U x)%Z -> (U x < p_flag \/ p_flag + 8 <= U x)%Z ->
    (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> UMG x = mem x.
  Proof using HG Hps HN Hmu Hcells Hsp thr c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start segs.
    intros x H1 H2 H3 H4. pose proof (u64_range sp). cells_split. destruct Hmu as (M0 & M8 & Mal). (lazymatch goal with |- ?G => let G' := eval unfold UMG, UMF in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply UME_o3; assumption | wd_ulia | wd_ulia | wd_ulia | wd_ulia].
  Qed.
  (* [comment removed for export] *)
  Lemma shz_keep : forall l M (x : word),
    Forall (fun bs => 0 <= fst bs /\ fst bs mod 8 = 0 /\ fst bs + snd bs <= 0x7fff8000 /\ 8 <= snd bs)%Z l ->
    Forall (fun bs => U x < zshad (fst bs) \/ zshad (fst bs) + snd bs / 8 <= U x)%Z l ->
    shz M l x = M x.
  Proof using Hps Hmu thr globs p_mu p_start dbase base.
    induction l as [|[b s] l IH]; intros M x Hok Hd; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [shz] in G in change_no_check G' end).
    apply Forall_cons_iff in Hok as [[Hb [Hb8 [Hbs Hs]]] Hok]. apply Forall_cons_iff in Hd as [Hd0 Hd]. cbn [fst snd] in Hb, Hb8, Hbs, Hs, Hd0.
    rewrite (IH _ x Hok Hd).
    pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono s (0x7fff8000 - b) 8 ltac:(lia) ltac:(lia)) as Hd'.
    replace ((0x7fff8000 - b) / 8)%Z with (0xffff000 - b / 8)%Z in Hd'
      by (replace (0x7fff8000 - b)%Z with ((0xffff000 - b / 8) * 8)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold zshad in Hd0 |- *.
    apply wbytes_outside; rewrite ?repeat_length, ?Z2Nat.id by lia; wd_ulia.
  Qed.
  Theorem UMG_band : forall x : word,
    (0x7fff8000 <= U x < 0x8fff8000)%Z ->
    Forall (fun bs => U x < zshad (fst bs) \/ zshad (fst bs) + snd bs / 8 <= U x)%Z ((p_start, 64 * N)%Z :: globs) ->
    UMG x = mem x.
  Proof using HG Hps HN Hmu Hcells Hsp thr c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start segs.
    intros x Hx Hl. pose proof (u64_range sp) as Hspr. pose proof zshad_ps as [Z1 Z2]. cells_split.
    destruct Hps as (P0 & P8 & Pend & PN). destruct Hmu as (M0 & M8 & Mal).
    apply Forall_cons_iff in Hl as [Hx0 Hl]. cbn [fst snd] in Hx0.
    replace (64 * N / 8)%Z with (8 * N)%Z in Hx0 by (replace (64 * N)%Z with (8 * N * 8)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold UMG, UMF, UME, ps_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length;
      [ | (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_at, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia .. ].
    (lazymatch goal with |- ?G => let G' := eval unfold UMD in G in change_no_check G' end). rewrite (shz_keep globs UMC x globs_ok Hl). apply UMC_out; lia.
  Qed.
  (* [comment removed for export] *)
  Theorem UMG_grows : mem_grows mem UMG.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold UMG in G in change_no_check G' end). eapply mem_grows_trans; [apply UMF_grows|]. grows_tac. Qed.
  (* [comment removed for export] *)
  Theorem UMG_mu : rdn segs UMG (Z_to_bv 64 p_mu) 8 = Some (LE8z 0).
  Proof using Hps Hmu Hcells_mu Hcells thr c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start.
    cells_split. destruct Hmu as (M0 & M8 & Mal). pose proof (cell_mu p_flag 8%nat ltac:((lazymatch goal with |- ?G => let G' := eval unfold ug_cells in G in change_no_check G' end); clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto) ltac:(lia)) as FM.
    cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.succ] in FM. (lazymatch goal with |- ?G => let G' := eval unfold UMG, UMF in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [| rewrite length_N_to_le_bytes; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.succ] in G in change_no_check G' end); lia ] | wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
    apply rdn_wbytes_hit8; wd_ulia.
  Qed.
  Theorem UMG_flag : rdn segs UMG (Z_to_bv 64 p_flag) 8 = Some (LE8z 0).
  Proof using Hcells c_ro c_inited g_pgsz p_aflags g_aflags g_stop g_start. cells_split. (lazymatch goal with |- ?G => let G' := eval unfold UMG in G in change_no_check G' end). apply rdn_wbytes_hit8; wd_ulia. Qed.
End UNREG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Abbreviation LE8z' z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Record unregH (segs : list Segment) (t : unreg_tab) (mem : word -> option byte)
       (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) : Prop := UNREGH {
  uh_sp : (0x10007fff8000 + 272 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z;
  uh_ret : ret_ok ra;
  (* [comment removed for export] *)
  uh_gs : rdn segs mem (Z_to_bv 64 (ut_g_start t)) 8 = Some (LE8z' (ut_p_start t));
  uh_ge : rdn segs mem (Z_to_bv 64 (ut_g_stop t)) 8 = Some (LE8z' (ut_p_start t + 64 * Z.of_nat (length (ut_globs t))));
  uh_fl : rdn segs mem (Z_to_bv 64 (ut_p_flag t)) 8 = Some (LE8 vflag);
  uh_fl_nz : U vflag <> 0%Z;
  uh_ga : rdn segs mem (Z_to_bv 64 (ut_g_aflags t)) 8 = Some (LE8z' (ut_p_aflags t));
  uh_rg : rdn segs mem (Z_to_bv 64 (ut_p_aflags t + 24)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  uh_mu : rdn segs mem (Z_to_bv 64 (ut_p_mu t)) 8 = Some (LE8z' 0);
  uh_ini : rdn segs mem (Z_to_bv 64 (ut_c_inited t)) 1 = Some [Z_to_bv 8 1];
  uh_cpm : rdn segs mem (Z_to_bv 64 (pt_c_cpm (ut_pt t))) 1 = Some [cpm];
  uh_cpm_nz : U cpm <> 0%Z;
  uh_gsh : rdn segs mem (Z_to_bv 64 (pt_g_shoff (ut_pt t))) 8 = Some (LE8z' (pt_p_shoff (ut_pt t)));
  uh_sh : rdn segs mem (Z_to_bv 64 (pt_p_shoff (ut_pt t))) 8 = Some (LE8z' 0x7fff8000);
  uh_gmb : rdn segs mem (Z_to_bv 64 (pt_g_midbeg (ut_pt t))) 8 = Some (LE8z' (pt_p_midbeg (ut_pt t)));
  uh_mb : rdn segs mem (Z_to_bv 64 (pt_p_midbeg (ut_pt t))) 8 = Some (LE8z' 0);
  uh_gme : rdn segs mem (Z_to_bv 64 (pt_g_midend (ut_pt t))) 8 = Some (LE8z' (pt_p_midend (ut_pt t)));
  uh_me : rdn segs mem (Z_to_bv 64 (pt_p_midend (ut_pt t))) 8 = Some (LE8 midend);
  uh_ghe : rdn segs mem (Z_to_bv 64 (pt_g_hiend (ut_pt t))) 8 = Some (LE8z' (pt_p_hiend (ut_pt t)));
  uh_he : rdn segs mem (Z_to_bv 64 (pt_p_hiend (ut_pt t))) 8 = Some (LE8z' 0x7fffffffffff);
  uh_grms : rdn segs mem (Z_to_bv 64 (pt_g_rms (ut_pt t))) 8 = Some (LE8z' (pt_p_rms (ut_pt t)));
  uh_rms : rdn segs mem (Z_to_bv 64 (pt_p_rms (ut_pt t))) 8 = Some (LE8 (pt_mset (ut_pt t)));
  uh_gcf : rdn segs mem (Z_to_bv 64 (pt_g_cfl (ut_pt t))) 8 = Some (LE8z' (pt_p_cfl (ut_pt t)));
  uh_thr : rdn segs mem (Z_to_bv 64 (pt_p_cfl (ut_pt t) + 120)) 8 = Some (LE8z' thr);
  uh_thr_rng : (0 <= thr < 2 ^ 64)%Z;
  uh_pg : rdn segs mem (Z_to_bv 64 (ut_g_pgsz t)) 8 = Some (LE8 pg);
  uh_ro : rdn segs mem (Z_to_bv 64 (ut_c_ro t)) 8 = Some (LE8 ro);
  (* [comment removed for export] *)
  uh_cells : Forall (fun c => 0 <= c /\ c + 8 <= 0x7fff8000)%Z
               (ut_g_start t :: ut_g_stop t :: ut_p_flag t :: ut_g_aflags t :: ut_p_aflags t :: (ut_p_aflags t + 24)%Z
                :: ut_c_inited t :: ut_g_pgsz t :: ut_c_ro t :: poison_cells (ut_pt t));
  uh_cells_mu : Forall (fun c => c + 8 <= ut_p_mu t \/ ut_p_mu t + 8 <= c)%Z
               (ut_g_start t :: ut_g_stop t :: ut_p_flag t :: ut_g_aflags t :: ut_p_aflags t :: (ut_p_aflags t + 24)%Z
                :: ut_c_inited t :: ut_g_pgsz t :: ut_c_ro t :: poison_cells (ut_pt t));
  uh_mu_rng : (64 <= ut_p_mu t)%Z /\ (ut_p_mu t + 16 <= 0x7fff8000)%Z /\ (ut_p_mu t mod 8 = 0)%Z;
  (* [comment removed for export] *)
  uh_N : (1 <= Z.of_nat (length (ut_globs t)))%Z;
  uh_ps : (0 <= ut_p_start t)%Z /\ (ut_p_start t mod 8 = 0)%Z
          /\ (ut_p_start t + 64 * Z.of_nat (length (ut_globs t)) <= 0x7fff8000)%Z /\ (8 * Z.of_nat (length (ut_globs t)) < thr)%Z;
  uh_ps_mu : (ut_p_start t + 64 * Z.of_nat (length (ut_globs t)) <= ut_p_mu t \/ ut_p_mu t + 8 <= ut_p_start t)%Z;
  uh_globs : forall i b s, nth_error (ut_globs t) i = Some (b, s) ->
    rdn segs mem (Z_to_bv 64 (ut_p_start t + 64 * Z.of_nat i)) 8 = Some (LE8z' b)
    /\ rdn segs mem (Z_to_bv 64 (ut_p_start t + 64 * Z.of_nat i + 16)) 8 = Some (LE8z' s)
    /\ rdn segs mem (Z_to_bv 64 (ut_p_start t + 64 * Z.of_nat i + 56)) 8 = Some (LE8z' (2 ^ 64 - 1))
    /\ (0 <= b)%Z /\ (b mod 8 = 0)%Z /\ (s mod 8 = 0)%Z /\ (8 <= s)%Z /\ (b + s <= 0x7fff8000)%Z /\ (s / 8 < thr)%Z
    /\ store_ok segs mem (Z_to_bv 64 (zshad b)) (Z.to_nat (s / 8)) = true;
  (* [comment removed for export] *)
  uh_stk : store_ok segs mem (at_ sp (-272)) 272 = true;
  uh_mu_ok : store_ok segs mem (Z_to_bv 64 (ut_p_mu t)) 8 = true;
  uh_fl_ok : store_ok segs mem (Z_to_bv 64 (ut_p_flag t)) 8 = true;
  uh_shd : store_ok segs mem (Z_to_bv 64 (zshad (ut_p_start t))) (Z.to_nat (8 * Z.of_nat (length (ut_globs t)))) = true;
  uh_mset_ok : ret_ok (pt_mset (ut_pt t));
  uh_mset_nz : U (pt_mset (ut_pt t)) <> 0%Z }.

(* [comment removed for export] *)
Definition ug_final (t : unreg_tab) (mem : word -> option byte) (sp ra pg : word) (regs : bvmap 5 word) : word -> option byte :=
  UMG (ut_base t) (ut_dtor t) (ut_pt t) (ut_p_start t) (ut_p_flag t) (ut_p_mu t) (ut_globs t) (ut_str t) mem sp ra pg regs.

Theorem unreg_globals_run : forall segs t, unreg_tab_ok segs t ->
  forall mem rom (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) regs,
  unregH segs t mem sp ra vflag cpm midend thr pg ro ->
  getr regs 1 = ra -> getr regs 2 = sp ->
  exists r,
    msteps segs (mkst regs (ut_dtor t) mem rom) (mkst r ra (ug_final t mem sp ra pg regs) rom)
    /\ regs_agree (fun x => In x unreg_clob) regs r.
Proof using.
  intros segs t TOK mem rom sp ra vflag cpm midend thr pg ro regs PRE R1 R2.
  destruct TOK. destruct PRE.
  rewrite <- (at_0 (ut_dtor t)). (lazymatch goal with |- ?G => let G' := eval unfold ug_final in G in change_no_check G' end).
  eapply unreg_run; eassumption.
Qed.

(* [comment removed for export] *)
Theorem ug_final_outside : forall segs t, unreg_tab_ok segs t ->
  forall mem (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) regs,
  unregH segs t mem sp ra vflag cpm midend thr pg ro ->
  forall x : word,
    (U x < U sp - 272 \/ U sp <= U x)%Z -> (U x < ut_p_mu t \/ ut_p_mu t + 8 <= U x)%Z ->
    (U x < ut_p_flag t \/ ut_p_flag t + 8 <= U x)%Z -> (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z ->
    ug_final t mem sp ra pg regs x = mem x.
Proof using.
  intros segs t TOK mem sp ra vflag cpm midend thr pg ro regs PRE x H1 H2 H3 H4.
  destruct TOK. destruct PRE. (lazymatch goal with |- ?G => let G' := eval unfold ug_final in G in change_no_check G' end).
  eapply UMG_outside; eassumption.
Qed.

(* [comment removed for export] *)
Theorem ug_final_band : forall segs t, unreg_tab_ok segs t ->
  forall mem (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) regs,
  unregH segs t mem sp ra vflag cpm midend thr pg ro ->
  forall x : word,
    (0x7fff8000 <= U x < 0x8fff8000)%Z ->
    Forall (fun bs => U x < zshad (fst bs) \/ zshad (fst bs) + snd bs / 8 <= U x)%Z
           ((ut_p_start t, 64 * Z.of_nat (length (ut_globs t)))%Z :: ut_globs t) ->
    ug_final t mem sp ra pg regs x = mem x.
Proof using.
  intros segs t TOK mem sp ra vflag cpm midend thr pg ro regs PRE x H1 H2.
  destruct TOK. destruct PRE. (lazymatch goal with |- ?G => let G' := eval unfold ug_final in G in change_no_check G' end).
  eapply UMG_band; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ug_final_mu : forall segs t, unreg_tab_ok segs t ->
  forall mem (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) regs,
  unregH segs t mem sp ra vflag cpm midend thr pg ro ->
  rdn segs (ug_final t mem sp ra pg regs) (Z_to_bv 64 (ut_p_mu t)) 8 = Some (LE8z' 0)
  /\ rdn segs (ug_final t mem sp ra pg regs) (Z_to_bv 64 (ut_p_flag t)) 8 = Some (LE8z' 0).
Proof using.
  intros segs t TOK mem sp ra vflag cpm midend thr pg ro regs PRE.
  destruct TOK. destruct PRE. (lazymatch goal with |- ?G => let G' := eval unfold ug_final in G in change_no_check G' end). split; [eapply UMG_mu | eapply UMG_flag]; eassumption.
Qed.

Theorem ug_final_grows : forall segs t, unreg_tab_ok segs t ->
  forall mem (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) regs,
  unregH segs t mem sp ra vflag cpm midend thr pg ro ->
  mem_grows mem (ug_final t mem sp ra pg regs).
Proof using.
  intros segs t TOK mem sp ra vflag cpm midend thr pg ro regs PRE.
  destruct TOK. destruct PRE. (lazymatch goal with |- ?G => let G' := eval unfold ug_final in G in change_no_check G' end).
  eapply UMG_grows; eassumption.
Qed.
End FPGen1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
