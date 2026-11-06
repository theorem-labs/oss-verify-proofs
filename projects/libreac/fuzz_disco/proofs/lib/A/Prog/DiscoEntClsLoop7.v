(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 179 of its 207 lines of code are new or changed and 41 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody
ClassifyCore ReacDiscoClassify ReacDiscoClassifyOnSegment CheckSighting ReacDiscoGateShouldPush DiscoEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cl7_after M :=
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M; clear HF;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

Ltac cl7_br BR W HS c :=
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    let a := eval vm_compute in (sr_get (ss_regs s) 23%bv) in
    let b := eval vm_compute in (sr_get (ss_regs s) 24%bv) in
    apply (BR W _ _ _ _ _ c a b HS)
  end.

Ltac cl7_reg HS r :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?s (restrict ?H ?m) =>
    rewrite (st_ok_pi_restrict_reg H E s m r HS);
    let e := eval vm_compute in (sr_get (ss_regs s) r) in change (sr_get (ss_regs s) r) with e
  end.

Ltac cl7_keep HS HROK :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), (HROK r);
  cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr.

Lemma cl7_atom : forall E sr regs (r : bv 5) n v, regs_ok E sr regs -> sr_get sr r = SOff n 0 ->
  getr regs r = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E sr regs r n v HR Hs Hg. rewrite <- sv_denot_SOff0, <- Hs, <- (HR r). exact Hg. Qed.

Lemma cl7_soff : forall E n u c v, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u + c = v ->
  sv_denot E (SOff n c) = Z_to_bv 64 v.
Proof.
intros E n u c v Hn Hu Hv Hc. rewrite denot_lit_U. f_equal. rewrite U_SOff, Hn, unsigned_lit_small by lia.
subst v. apply zcanon_id. unfold M64. lia.
Qed.

Lemma cl7_r19 : forall E f n F o k v, ew E f = Z_to_bv 64 F -> ew E n = Z_to_bv 64 k ->
  0 <= F -> 0 <= o -> 0 <= k -> F + o + 32 * k < 2 ^ 64 -> F + o + 32 * k = v ->
  sv_denot E (SAlu ALU_ADD (SOff f o) (SAlu ALU_SLL (SOff n 0) (SLit 5))) = Z_to_bv 64 v.
Proof.
intros E f n F o k v Hf Hn HF Ho Hk Hlt Hv. subst v. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SOff, U_SAlu, U_SOff, U_SLit. cbn [zalu_raw].
rewrite Hf, Hn, !unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id 5), (zcanon_id k), (zcanon_id (F + o)) by (unfold M64; lia).
change (Z.land 5 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
rewrite (zcanon_id (k * 32)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Ltac cl7_in := cbv [In]; repeat (first [left; reflexivity | right]).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.

Lemma cl7_rL : forall cx regs regs', d_rL B cx regs ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr regs' r = getr regs r) -> d_rL B cx regs'.
Proof.
intros cx regs regs' (L2 & L3 & L4 & L8 & L9 & L18 & L20 & L25) K. unfold d_rL, spZ in *.
rewrite (K 2%bv), (K 3%bv), (K 4%bv), (K 8%bv), (K 9%bv), (K 18%bv), (K 20%bv), (K 25%bv) by cl7_in.
repeat split; assumption.
Qed.

Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Lemma cl7_land : forall (fq : YK11.FPState) (cx : dcx) (pc kmax accmax : Z)
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  (W : world SEGS) ly3 S3 mem3 md' k acc E ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax -> mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall md, P (ms_regs ms) ly3 S3 W mem3 md) ->
  DAT cx pc kmax accmax P W (mkCfg ms md').
Proof.
intros fq cx pc kmax accmax P W ly3 S3 mem3 md' k acc E ss ms Hf0 HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc MEQ HP.
assert (Em : ms_mem ms = mem3) by (apply functional_extensionality; exact MEQ).
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), mem3, md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc, Em; reflexivity|].
rewrite Em in HJ.
split; [exact Hf0|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|]. exact (HP md').
Qed.

Theorem cl_L7 : cl_L7_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_L7_stmt. intros cx h i n now op nb fr len nn k W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k0 & acc & -> & Hf0 & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  HLM & Hkn & H23 & H24 & H21 & H26).
destruct HLM as (Sg & G & push & HBS & HSG & HGT & HGN & HSPL).
pose proof HBS as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbc & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
pose proof HGT as (_ & _ & (_ & HGb & _)). rewrite HGN in HGb.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k0) by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k0 HC) as (HS16 & HSlo & HShi & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HOG : d_obj cx OG = d_FB cx + 2624) by reflexivity.
pose proof (cl_regs_ok B cx E regs [] HdE HrL HAr2) as HROK.
assert (A554 : ew (d_env cx E (cl_vals regs [])) 554 = Z_to_bv 64 k)
  by exact (cl7_atom _ _ _ 23%bv 554%nat k HROK ltac:(vm_compute; reflexivity) H23).
assert (A555 : ew (d_env cx E (cl_vals regs [])) 555 = Z_to_bv 64 nn)
  by exact (cl7_atom _ _ _ 24%bv 555%nat nn HROK ltac:(vm_compute; reflexivity) H24).
assert (A552 : ew (d_env cx E (cl_vals regs [])) 552 = Z_to_bv 64 (d_obj cx OG + 32 + 32 * k))
  by exact (cl7_atom _ _ _ 21%bv 552%nat _ HROK ltac:(vm_compute; reflexivity) H21).
assert (A557 : ew (d_env cx E (cl_vals regs [])) 557 = Z_to_bv 64 (nn - 1 - k))
  by exact (cl7_atom _ _ _ 26%bv 557%nat _ HROK ltac:(vm_compute; reflexivity) H26).
assert (A516 : ew (d_env cx E (cl_vals regs [])) 516 = Z_to_bv 64 (d_FB cx)).
{ rewrite d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & HF & _). exact HF. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k0 E 0xd80 cl_sr
  (cl_vals regs []) [] [] [] (d_facts [] []) HC HdE Hregs Hflag HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k0 E (cl_vals regs []) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
pose proof (d_E_env cx E (cl_vals regs []) HdE) as HEd.
pose proof HEd as (_ & _ & HEI & _).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_disco) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xd80)) with (Z_to_bv 64 (BASE + 0xd80)).
paj_run_to_sh RUNTO HS HJ 0xdd0; [awr_ok_tac|].
cl7_after M1.
cl7_br BR W HS BC_GEU; intros Hc1 HS1; clear HS;
  rewrite branch_geu_U, (U_atom_off _ 554%nat k 1 A554), (U_atom _ 555%nat nn A555) in Hc1 by lia.
- apply negb_true_iff, Z.ltb_ge in Hc1.
  paj_run_to_sh RUNTO HS1 HJ 0xdd0; [awr_ok_tac|].
  cl7_after M2.
  cl7_br BR W HS1 BC_NE; intros Hc2 HS2; clear HS1;
    rewrite branch_ne_U, (U_atom_off _ 554%nat k 1 A554), (U_atom _ 555%nat nn A555) in Hc2 by lia.
  + apply negb_true_iff, Z.eqb_neq in Hc2. exfalso. lia.
  + paj_run_to_sh RUNTO HS2 HJ 0xdd0; [awr_ok_tac|].
    cl7_after M3.
    apply SRr_ret. left. unfold cl_X.
    lazymatch goal with |- context [mkCfg ?m _] =>
      assert (K : forall r, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs m) r = getr regs r)
        by cl7_keep HS2 HROK end.
    eapply (cl7_land fq cx 0xdd0 _ _ _ W ly3 S3 mem3 _ k0 acc _ _ _ Hf0 HB HJ HFR Hk Hev Hmo Hacc HS2 eq_refl eq_refl).
    * intros x. rewrite M3, M2, M1. reflexivity.
    * intros md. exists Sg, push. split; [|exact (conj HSG HSPL)].
      unfold cl_base. refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj Hsp0 (conj Hfrm
        (conj H248 (conj H408 (conj H392 (conj Hlen (conj Hnb (conj Hnbc Hbody)))))))))))))).
      exact (cl7_rL cx regs _ HrL K).
- apply negb_false_iff, Z.ltb_lt in Hc1.
  paj_run_to_sh RUNTO HS1 HJ 0xda0; [awr_ok_tac|].
  cl7_after M2.
  apply SRr_ret. right. unfold cl_LJ.
  lazymatch goal with |- context [mkCfg ?m _] =>
    assert (K : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 24; 25; 26]%bv -> getr (ms_regs m) r = getr regs r)
      by cl7_keep HS1 HROK end.
  eapply (cl7_land fq cx 0xda0 _ _ _ W ly3 S3 mem3 _ k0 acc _ _ _ Hf0 HB HJ HFR Hk Hev Hmo Hacc HS1 eq_refl eq_refl).
  + intros x. rewrite M2, M1. reflexivity.
  + intros md. split.
    * exists Sg, G, push. split; [|exact (conj HSG (conj HGT (conj HGN HSPL)))].
      unfold cl_base. refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj Hsp0 (conj Hfrm
        (conj H248 (conj H408 (conj H392 (conj Hlen (conj Hnb (conj Hnbc Hbody)))))))))))))).
      apply (cl7_rL cx regs _ HrL). intros r Hr. apply K. cbv [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cl7_in.
    * unfold cl_jregs.
      split; [lia|]. split; [lia|].
      split; [cl7_reg HS1 (23%bv : bv 5); apply (cl7_soff _ 554%nat k); [exact A554 | lia | lia | lia]|].
      split; [rewrite (K 24%bv) by cl7_in; exact H24|].
      split; [rewrite (K 21%bv) by cl7_in; exact H21|].
      split; [rewrite (K 26%bv) by cl7_in; exact H26|].
      split; [cl7_reg HS1 (19%bv : bv 5); apply (cl7_r19 _ 516%nat 554%nat (d_FB cx) 2624 k);
        [exact A516 | exact A554 | lia | lia | lia | lia | lia]|].
      split; [cl7_reg HS1 (22%bv : bv 5); apply (cl7_soff _ 552%nat (d_obj cx OG + 32 + 32 * k)); [exact A552 | lia | lia | lia]|].
      cl7_reg HS1 (27%bv : bv 5); apply (cl7_soff _ 557%nat (nn - 1 - k)); [exact A557 | lia | lia | lia].
Qed.
End h.
End f.
End d.
